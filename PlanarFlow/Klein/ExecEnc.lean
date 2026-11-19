module

public import PlanarFlow.Klein.ProgExists
public import WordRAM.Machine.WordMono
public import WordRAM.Machine.KernelRfl

/-!
# Klein's program from any configuration holding the encoding in memory

`PlanarFlow.Klein.klein_exec` runs `kleinProg` from any configuration `c₀` bounded by
`B + 16 (n + 1)` holding five real constants and weights, but it reads the **encoding of the
one-face instance from its input** `P` (`readIn`: `KInput`, `KBnd`, `KOut`, `KTgt`, `KInit` are
predicates on the words `P.data`), and `klein_exec_exists` chooses that input, the start
configuration and the word bound inside its proof. In one run of a node there is a single input,
so here the encoding is read from **memory**:

* `kleinProgMem B nD n k t β len = (kleinProg B nD n k t).toMem 201 β len`: every
  `readIn r a` replaced by `r201 := β; r201 := r201 + a; r := nmem r201` (and `inputSize`, which
  `kleinProg` does not use, by `r := len`); `kleinProg` names only the registers `< 201` and
  uses no random word (`kleinProg_regsOK`, `kleinProg_noRand`, checked by the kernel).
* **The encoding predicate** (`KleinEnc`): the words `P.data.getD i 0`, `i ≤ B + 16 (n + 1)`,
  at `β + i`, above the word bound of Klein's run (`InData`), where `P` is any input word list
  meeting the hypotheses of `klein_exec` (the map, the boundary, the out-darts, the targets, the
  initial trees and cotree: `KInput`, `KBnd`, `KOut`, `KTgt`, `KInit`, and the bound `hP`), plus
  the real memory of `klein_exec` (`aWT`, `aPH`, `aTL`, `aTH`, `aH0`).
* `klein_exec_of_enc`: from **any** configuration `d` with any word bound `W'` holding the
  encoding (with its registers `< 201` and its memory at addresses `≤ B + 16 (n + 1)` bounded by
  that bound), `kleinProgMem` runs on **any** input within `3 ×` the bound of `klein_exec`, makes
  the trip and leaves the answers `kOut` in `d'`, keeping the output, the registers `> 201`
  (natural) and `≥ 201` (real), the encoding and all the memory above `B + 16 (n + 1)`.
* `klein_exec_enc_exists`: the packaging of `klein_exec_exists` with the encoding explicit: for
  every instance there are `n`, `B` and input words `Pk.data` (the encoding, `kInputT`) such
  that the run exists from every configuration holding them at any base `β` above the word bound
  (and the real constants).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace Klein

open Finset CombMap MSSP STFlow DynTree WordRAM WordRAM.Machine WordRAM.Machine.Stmt

/-- `kleinProg` names only the registers `< 201` (checked by the kernel). -/
theorem kleinProg_regsOK (B nD n k t : ℕ) :
    (kleinProg B nD n k t).regsOK (fun r => decide (r < 201)) = true := by
  kernel_rfl

/-- `kleinProg` uses no random word (checked by the kernel). -/
theorem kleinProg_noRand (B nD n k t : ℕ) : (kleinProg B nD n k t).noRand = true := by
  kernel_rfl

/-- **Klein's program reading its encoding from memory** at the base `β`, with the scratch
register `r201`. -/
def kleinProgMem (B nD n k t β len : ℕ) : Stmt := (kleinProg B nD n k t).toMem 201 β len

/-- The register predicate of `kleinProg`. -/
abbrev kU : ℕ → Bool := fun r => decide (r < 201)

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F]
variable {M : CombMap D V F} {k : ℕ} {g : ℕ → D} {S : Finset D} {ℓ : D → ℤ} {nD : ℕ}
  {σ : D ≃ Fin nD} {n : ℕ} {ιv : V → ℕ} {ιg : D → ℕ} {ιf : F → ℕ} {ιe : D → ℕ} {t : ℕ}
  {X : ℕ → V}

local notation "𝒢" => pieceGraph M S ℓ

/-- **The encoding in memory**: the input words of `P` at `β + i` for `i ≤ B + 16 (n + 1)`
(above that bound), and the real constants of `klein_exec` (the weights `tripWt 0`, `tripφ`,
`tripL`, `tripTh`, `tripH0`). -/
structure KleinEnc (M : CombMap D V F) (k : ℕ) (g : ℕ → D) (S : Finset D) (ℓ : D → ℤ)
    (σ : D ≃ Fin nD) (B n β W' : ℕ) (P : Input) (d : Config) : Prop where
  dat : InData P (B + 16 * (n + 1)) β P.data.length W' d
  wt : ∀ x, d.rmem (aWT + σ x) = tripWt M k g S ℓ 0 x
  ph : ∀ x, d.rmem (aPH nD + σ x) = tripφ S ℓ x
  tl : d.rmem (aTL nD) = tripL V S ℓ
  th : d.rmem (aTH nD) = tripTh V S ℓ
  h0 : d.rmem (aH0 nD) = tripH0 V S ℓ k

/-- **Klein's algorithm from any configuration holding the encoding.** Under the hypotheses of
`klein_exec` on the input words `P`, from any configuration `d` bounded by `W'` holding the
encoding (`KleinEnc`), with its registers `< 201` and its memory at addresses
`≤ B + 16 (n + 1)` bounded by `B + 16 (n + 1)`, the program `kleinProgMem` runs on any input
`P'` within three times the bound of `klein_exec`; it makes the `k` moves of the trip, leaves
the answers `kOut` (distances in the piece from the sources of the moves to the targets) in the
final configuration, keeps the output, the natural registers `> 201`, the real registers
`≥ 201`, and all the memory above `B + 16 (n + 1)` (hence the encoding); the natural memory at
addresses `≤ B + 16 (n + 1)` stays bounded by `B + 16 (n + 1)`. -/
theorem klein_exec_of_enc {P P' : Input} {B : ℕ} (hWa : 9 * nD + 7 * n + k + 4 + 2 * t ≤ B)
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
  obtain ⟨c', steps, e, hsteps, htrip, hdist, hout⟩ := klein_exec hWa hB hOUT hRB hP H hR hL hK
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

/-- **The encoding exists for every instance.** For every map, boundary, piece and lengths
meeting the hypotheses of the trip and `t` targets that are not roots, there are `n`, a word
bound `B`, a numbering `σ` of the darts and input words `Pk.data` (the encoding of the one-face
instance, `kInputT`) such that from **every** configuration `d` with any word bound `W'`
holding `Pk.data` at any base `β > B + 16 (n + 1)` (with `β + B + 16 (n + 1) ≤ W'`) and the real
constants, with its registers `< 201` and its memory at addresses `≤ B + 16 (n + 1)` bounded by
`B + 16 (n + 1)`, `kleinProgMem` runs on any input within three times the bound of
`klein_exec_exists` with the answers `kOut` and the frame of `klein_exec_of_enc`. -/
theorem klein_exec_enc_exists (H : Hyp M k g S ℓ) (hR : SameReach M k g S ℓ) (t : ℕ)
    (X : ℕ → V) (hX : ∀ i < t, ¬ IsRoot M k g (X i)) :
    ∃ (n B : ℕ) (σ : D ≃ Fin (Fintype.card D)) (Pk : Input),
      n = 2 * (Fintype.card V + Fintype.card F + Fintype.card D) ∧
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
            (odist 𝒢 (tripSrc M k g j) (X i)).map ((↑) : ℤ → ℝ)) ∧
          d'.output = d.output ∧ (∀ r, 201 < r → d'.nreg r = d.nreg r) ∧
          (∀ r, 201 ≤ r → d'.rreg r = d.rreg r) ∧
          (∀ a, B + 16 * (n + 1) < a → d'.nmem a = d.nmem a) ∧
          (∀ a, B + 16 * (n + 1) < a → d'.rmem a = d.rmem a) ∧
          (∀ a ≤ B + 16 * (n + 1), d'.nmem a ≤ B + 16 * (n + 1)) := by
  obtain ⟨n, ιv, ιg, ιf, ιe, σ, P, B, T, C, vs, ts, fs, cs, c₀, hn, hWa, hB, hOUT, hRB, hP, hL,
    hK, hG, hO, hXT, hI, hoff, hCr, hT, -, -, -, -, -, -⟩ := klein_exec_pre H hR t X hX
  refine ⟨n, B, σ, P, hn, fun P' W' β d hd hrb hmb hE => ?_⟩
  obtain ⟨d', steps, e, hs, htrip, hdist, ho, h1, h2, h3, h4⟩ :=
    klein_exec_of_enc (P := P) (P' := P') hWa hB hOUT hRB hP H hR hL hK hG hO hXT hI hoff hCr
      hT d hd hrb hmb hE
  refine ⟨d', steps, e, hs.trans ?_, htrip, hdist, ho, h1, h2, h3, h4⟩
  have hk := H.k_le_card
  have h2' := H.face.two_le
  have hS : S.card ≤ Fintype.card D := card_le_univ S
  rw [hn]
  have := klein_steps_le (by omega) hS hk (t := t) (nV := Fintype.card V)
    (nF := Fintype.card F)
  omega

end Klein

end PlanarFlow
