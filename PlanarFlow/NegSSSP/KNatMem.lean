module

public import PlanarFlow.NegSSSP.KEncVal
public import PlanarFlow.Klein.DivRead
public import PlanarFlow.Klein.CmpEmbed

/-!
# Klein's program reading its encoding from memory, on natural words

At a node of the negative-length recursion Klein's program reads its encoding from memory
(`Klein.kleinProgMem`, the input words at `β`, the real constants at the addresses `aWT + σ x`,
…). This file runs that program **on natural words**, inside any natural configuration that
holds the encoding:

* `Klein.kConst`: the real constants of the encoding (`tripWt`, `tripφ`, `tripL`, `tripTh`,
  `tripH0`) as integers by address, `0` elsewhere.
* `Klein.KleinEncN`: the natural form of the encoding: the input words at `β` (`InData`), and at
  `βK + a` (`a ≤ WK < βK`) the residue modulo `Mo` of the constant at `a`.
* `Klein.kleinMemN`: the constants `Mo = 2 Hc + 1`, `Hc`, `βK` into the registers `404`,
  `405`, `406`, then `ModNat.toNat 202 Mo (kleinProgMem …)`: the reals of Klein's program kept
  modulo `Mo` in the natural registers `202 + r` and the natural memory `βK + a`.
  `kleinMemN_natOnly`: **no real instruction** (checked by the kernel).
* `Klein.klein_memN`: under `KVal` (the hypotheses of `klein_exec_of_enc`), from **every**
  natural configuration holding `KleinEncN`, with the registers `< 404` cleared, its memory
  `≤ WK` bounded by `WK` and the work space bounded by its bound, `kleinMemN` runs within
  `4 · 3 · 36500000 (N lg N + k t lg N) + 3` steps (`N` the size of the map) with words at most
  any `WN ≥ βK + WK + Mo² + Mo`, and **the natural answers (`kOutNK`) are the distances**; it
  keeps the natural registers `≥ 408`, the natural memory above the work space outside
  `[βK, βK + WK]`, all reals and the output.
* `Klein.klein_memNDC`: the same followed by `divCutLoop` (the answers divided by `N₁` with
  `divN` and cut off at `Wc`).

The proof lifts the natural configuration to a real one (`liftK`: the reals are the constants of
the encoding), runs Klein's real program there (`klein_exec_val`), bounds its comparisons by
`Hc ≥ kleinHI` (`kleinProgMem_cmpOK`) and simulates it (`ModNat.ExecCmp.toNat_consts`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace NegSSSP

open WordRAM WordRAM.Machine

/-- **The registers outside `U` are kept** by every run of a statement naming only the
registers in `U`, with no input and no random word (`exec_frame` and determinism). -/
theorem exec_nreg_keep {I : Input} {W : ℕ} {s : Stmt} {c c' : Config} {k : ℕ} {U : ℕ → Bool}
    (h : Exec I W s c c' k) (hs : s.regsOK U = true) (hn : s.noInp = true)
    (hr : s.noRand = true) : ∀ r, U r = false → c'.nreg r = c.nreg r := by
  obtain ⟨d', e, -, hK, -⟩ := exec_frame h hs hn hr
  obtain ⟨rfl, -⟩ := Exec.det h e
  exact hK.nreg

end NegSSSP

namespace Klein

open Finset CombMap MSSP STFlow DynTree WordRAM WordRAM.Machine WordRAM.Machine.Stmt

/-! ### The program -/

/-- **Klein's program reading its encoding from memory, on natural words**: the constants
`Mo = 2 Hc + 1`, `Hc`, `βK` into the registers `404`, `405`, `406`, then `kleinProgMem` with
its reals kept modulo `Mo` (real register `r` at the natural register `202 + r`, real cell `a` at
the natural cell `βK + a`, `a ≤ WK < βK`). -/
def kleinMemN (B nD n k t β len Hc βK : ℕ) : Stmt :=
  .seq (ModNat.constsS 202 (2 * Hc + 1) Hc βK)
    (ModNat.toNat 202 (2 * Hc + 1) (kleinProgMem B nD n k t β len))

/-- **`kleinMemN` has no real instruction and no real test** (checked by the kernel). -/
theorem kleinMemN_natOnly (B nD n k t β len Hc βK : ℕ) :
    natOnly (kleinMemN B nD n k t β len Hc βK) = true := by
  kernel_rfl

/-- `kleinMemN`, then the answers divided by `N` and cut off at `Wc` (`divCutLoop`). -/
def kleinMemNDC (B nD n k t β len Hc βK N Wc : ℕ) : Stmt :=
  .seq (kleinMemN B nD n k t β len Hc βK) (divCutLoop (βK + aOUT nD) (aRB n) (k * t) N Wc)

/-- **`kleinMemNDC` has no real instruction and no real test.** -/
theorem kleinMemNDC_natOnly (B nD n k t β len Hc βK N Wc : ℕ) :
    natOnly (kleinMemNDC B nD n k t β len Hc βK N Wc) = true := by
  show (natOnly (kleinMemN B nD n k t β len Hc βK) && natOnly (divCutLoop _ _ _ N Wc)) = true
  rw [kleinMemN_natOnly, divCutLoop_natOnly]; rfl

/-! ### The encoding on natural words -/

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F]

variable (V) in
/-- **The real constants of the encoding by address** (`KleinEnc`): `tripWt 0` at `aWT + σ x`,
`tripφ` at `aPH nD + σ x`, `tripL`, `tripTh`, `tripH0` at `aTL nD`, `aTH nD`, `aH0 nD`; `0`
elsewhere. -/
noncomputable def kConst (M : CombMap D V F) (k : ℕ) (g : ℕ → D) (S : Finset D) (ℓ : D → ℤ)
    {nD : ℕ} (σ : D ≃ Fin nD) (a : ℕ) : ℤ :=
  if h : a < nD then tripWt M k g S ℓ 0 (σ.symm ⟨a, h⟩)
  else if h' : a < 2 * nD then tripφ S ℓ (σ.symm ⟨a - nD, by omega⟩)
  else if a = 3 * nD then tripL V S ℓ
  else if a = 3 * nD + 1 then tripTh V S ℓ
  else if a = 3 * nD + 2 then tripH0 V S ℓ k
  else 0

section KConst

variable {M : CombMap D V F} {k : ℕ} {g : ℕ → D} {S : Finset D} {ℓ : D → ℤ} {nD : ℕ}
  {σ : D ≃ Fin nD}

lemma kConst_wt (x : D) : kConst V M k g S ℓ σ (aWT + σ x) = tripWt M k g S ℓ 0 x := by
  have h := (σ x).isLt
  unfold kConst aWT
  simp

lemma kConst_ph (x : D) : kConst V M k g S ℓ σ (aPH nD + σ x) = tripφ S ℓ x := by
  have h := (σ x).isLt
  unfold kConst aPH
  have h1 : ¬ nD + (σ x : ℕ) < nD := by omega
  have h2 : nD + (σ x : ℕ) < 2 * nD := by omega
  simp only [h1, h2, ↓reduceDIte]
  have : (⟨nD + (σ x : ℕ) - nD, by omega⟩ : Fin nD) = σ x := Fin.ext (by simp)
  simp [this]

lemma kConst_tl : kConst V M k g S ℓ σ (aTL nD) = tripL V S ℓ := by
  unfold kConst aTL
  have h1 : ¬ 3 * nD < nD := by omega
  have h2 : ¬ 3 * nD < 2 * nD := by omega
  simp only [h1, h2, ↓reduceDIte, ↓reduceIte]

lemma kConst_th : kConst V M k g S ℓ σ (aTH nD) = tripTh V S ℓ := by
  unfold kConst aTH
  have h1 : ¬ 3 * nD + 1 < nD := by omega
  have h2 : ¬ 3 * nD + 1 < 2 * nD := by omega
  have h3 : ¬ 3 * nD + 1 = 3 * nD := by omega
  simp only [h1, h2, h3, ↓reduceDIte, ↓reduceIte]

lemma kConst_h0 : kConst V M k g S ℓ σ (aH0 nD) = tripH0 V S ℓ k := by
  unfold kConst aH0
  have h1 : ¬ 3 * nD + 2 < nD := by omega
  have h2 : ¬ 3 * nD + 2 < 2 * nD := by omega
  have h3 : ¬ 3 * nD + 2 = 3 * nD := by omega
  have h4 : ¬ 3 * nD + 2 = 3 * nD + 1 := by omega
  simp only [h1, h2, h3, h4, ↓reduceDIte, ↓reduceIte]

lemma kConst_high {a : ℕ} (ha : 3 * nD + 3 ≤ a) : kConst V M k g S ℓ σ a = 0 := by
  unfold kConst
  have h1 : ¬ a < nD := by omega
  have h2 : ¬ a < 2 * nD := by omega
  have h3 : ¬ a = 3 * nD := by omega
  have h4 : ¬ a = 3 * nD + 1 := by omega
  have h5 : ¬ a = 3 * nD + 2 := by omega
  simp only [h1, h2, h3, h4, h5, ↓reduceDIte, ↓reduceIte]

end KConst

lemma resW_zero (M : ℕ) : resW M ((0 : ℤ) : ℝ) = 0 := by simp [resW]

/-- **The encoding on natural words**: the input words of `P` at `β` (`InData`, below `WK`),
and at `βK + a`, for every `a ≤ WK`, the residue modulo `Mo` of the real constant at `a`
(`kConst`). -/
structure KleinEncN (M : CombMap D V F) (k : ℕ) (g : ℕ → D) (S : Finset D) (ℓ : D → ℤ)
    {nD : ℕ} (σ : D ≃ Fin nD) (B n β WK βK Mo : ℕ) (P : Input) (d : Config) : Prop where
  dat : InData P (B + 16 * (n + 1)) β P.data.length WK d
  res : ∀ a ≤ WK, d.nmem (βK + a) = resW Mo (kConst V M k g S ℓ σ a : ℝ)

/-- The real configuration lifted from a natural one: the natural registers `< 202` and memory
`≤ WK`, the real constants `ρ` at the addresses `≤ WK`, nothing else. -/
noncomputable def liftK (WK : ℕ) (ρ : ℕ → ℤ) (d : Config) : Config where
  pc := d.pc
  nreg r := if r < 202 then d.nreg r else 0
  rreg _ := 0
  nmem a := if a ≤ WK then d.nmem a else 0
  rmem a := if a ≤ WK then (ρ a : ℝ) else 0
  output := d.output

/-! ### The run -/

variable {M : CombMap D V F} {k : ℕ} {g : ℕ → D} {S : Finset D} {ℓ : D → ℤ}

local notation "𝒢" => pieceGraph M S ℓ

set_option maxHeartbeats 1000000 in
/-- **Klein's program reading its encoding from memory, on natural words** (see the module
docstring). -/
theorem klein_memN (H : Hyp M k g S ℓ) (hR : SameReach M k g S ℓ) {t : ℕ} {X : ℕ → V}
    {n B : ℕ} {σ : D ≃ Fin (Fintype.card D)} {Pk : Input}
    (hn : n = 2 * (Fintype.card V + Fintype.card F + Fintype.card D))
    (hv : KVal M k g S ℓ σ n B t X Pk) {Hc : ℕ} (hHc : kleinHI V F S ℓ k ≤ Hc)
    {β WK βK WN : ℕ} (hβK : WK < βK) (hWN : βK + WK + (2 * Hc + 1) * (2 * Hc + 1) + (2 * Hc + 1) ≤ WN)
    (P' : Input) (d : Config) (hd : WordsBounded WN d) (hr : ∀ r < 404, d.nreg r = 0)
    (hm : ∀ a ≤ WK, d.nmem a ≤ WK) (hlow : ∀ a ≤ B + 16 * (n + 1), d.nmem a ≤ B + 16 * (n + 1))
    (hE : KleinEncN M k g S ℓ σ B n β WK βK (2 * Hc + 1) Pk d) :
    ∃ d' steps,
      Exec P' WN (kleinMemN B (Fintype.card D) n k t β Pk.data.length Hc βK) d d' steps ∧
      steps ≤ 4 * (3 * (36500000 * ((Fintype.card V + Fintype.card F + Fintype.card D) *
          BKMNW.lg (Fintype.card V + Fintype.card F + Fintype.card D) +
        k * t * BKMNW.lg (Fintype.card V + Fintype.card F + Fintype.card D)))) + 3 ∧
      (∀ j < k, ∀ i < t, kOutNK (Fintype.card D) n t βK d' j i =
        odist 𝒢 (tripSrc M k g j) (X i)) ∧
      d'.output = d.output ∧ (∀ r, 408 ≤ r → d'.nreg r = d.nreg r) ∧
      (∀ a, B + 16 * (n + 1) < a → (a ≤ WK ∨ (a < βK ∨ βK + WK < a)) → d'.nmem a = d.nmem a) ∧
      d'.rreg = d.rreg ∧ d'.rmem = d.rmem ∧
      (∀ a ≤ B + 16 * (n + 1), d'.nmem a ≤ B + 16 * (n + 1)) ∧
      (∀ a ≤ WK, d'.nmem (βK + a) < 2 * Hc + 1) ∧
      aOUT (Fintype.card D) + k * t ≤ B ∧ aRB n + k * t ≤ B := by
  obtain ⟨ιv, ιg, ιf, ιe, T, C, vs, ts, fs, cs, hWa, hB, hOUT, hRB, hP, hL, hK, hG, hO, hXT, hI,
    hoff, hCr, hT⟩ := hv
  have hv' : KVal M k g S ℓ σ n B t X Pk := ⟨ιv, ιg, ιf, ιe, T, C, vs, ts, fs, cs, hWa, hB, hOUT,
    hRB, hP, hL, hK, hG, hO, hXT, hI, hoff, hCr, hT⟩
  set Kw := B + 16 * (n + 1) with hKw
  set Mo := 2 * Hc + 1 with hMo
  have hσ : ∀ x : D, (σ x : ℕ) < Fintype.card D := fun x => (σ x).2
  have hdat := hE.dat
  have hβ1 := hdat.lt
  have hβ2 := hdat.le
  -- the lifted real configuration
  set c := liftK WK (kConst V M k g S ℓ σ) d with hc
  have hcw : WordsBounded WK c := by
    refine ⟨fun r => ?_, fun a => ?_⟩
    · simp only [hc, liftK]; split_ifs with h
      · rw [hr r (by omega)]; exact Nat.zero_le _
      · exact Nat.zero_le _
    · simp only [hc, liftK]; split_ifs with h
      · exact hm a h
      · exact Nat.zero_le _
  have hrb : ∀ r < 201, c.nreg r ≤ Kw := fun r hr' => by
    have h' : r < 202 := by omega
    simp only [hc, liftK, h', ↓reduceIte, hr r (by omega)]; exact Nat.zero_le _
  have hmb : ∀ a ≤ Kw, c.nmem a ≤ Kw := fun a ha => by
    have h' : a ≤ WK := by omega
    simp only [hc, liftK, h', ↓reduceIte]; exact hlow a ha
  have hcm : ∀ a ≤ WK, c.rmem a = (kConst V M k g S ℓ σ a : ℝ) := fun a ha => by
    simp only [hc, liftK, ha, ↓reduceIte]
  have hnD : 3 * Fintype.card D + 2 ≤ WK := by unfold aOUT at hOUT; omega
  have hEc : KleinEnc M k g S ℓ σ B n β WK Pk c := by
    refine ⟨⟨hdat.lt, hdat.le, hdat.len, fun i hi => ?_⟩, fun x => ?_, fun x => ?_, ?_, ?_, ?_⟩
    · have h' : β + i ≤ WK := by omega
      simp only [hc, liftK, h', ↓reduceIte]; exact hdat.mem i hi
    · rw [hcm _ (by have := hσ x; unfold aWT; omega), kConst_wt]
    · rw [hcm _ (by have := hσ x; unfold aPH; omega), kConst_ph]
    · rw [hcm _ (by unfold aTL; omega), kConst_tl]
    · rw [hcm _ (by unfold aTH; omega), kConst_th]
    · rw [hcm _ (by unfold aH0; omega), kConst_h0]
  -- the real run
  obtain ⟨c', steps, e, hs, -, hdist, ho, h1, h2, h3, h4, h5⟩ :=
    klein_exec_val H hR hn hv' P' WK β c hcw hrb hmb hEc
  have hcmp := kleinProgMem_cmpOK (P := Pk) (P' := P') hWa hB hOUT hRB hP H hR hL hK hG hO hXT hI
    hoff hCr hT c hcw hrb hmb hEc hHc
  -- the simulation
  have hS : ModNat.Sim 202 WK Mo βK c d := by
    refine ⟨fun r hr' => ?_, fun r hr' => ?_, fun a ha => ?_, fun a ha => ?_, rfl⟩
    · simp only [hc, liftK, hr', ↓reduceIte]
    · simp only [hc, liftK]
      rw [hr (202 + r) (by omega)]
      exact_mod_cast ModNat.res_nat (M := Mo) (z := 0) (by omega)
    · simp only [hc, liftK, ha, ↓reduceIte]
    · rw [hcm a ha, hE.res a ha]
      exact res_resW (by omega) _
  obtain ⟨d', k', ex, hk', hS', -, hfr, hfm, hfrr, hfrm⟩ := ModNat.ExecCmp.toNat_consts
    (hcmp.exec e) (kleinProgMem_regsOK _ _ _ _ _ _ _) (kleinProgMem_noDivR _ _ _ _ _ _ _)
    (M := Mo) (H := Hc) (by omega) (β := βK) (W' := WN) hβK (by omega) (by omega)
    (by omega) hS hd
  refine ⟨d', k', ex, ?_, fun j hj i hi => ?_, ?_, fun r hr' => hfr r (by omega),
    fun a ha ha' => ?_, hfrr, hfrm, fun a ha => ?_, fun a ha => ?_, hOUT, hRB⟩
  · have := Nat.mul_le_mul_left 4 hs
    omega
  · -- the answers
    have hq : j * t + t ≤ k * t := by
      have := Nat.mul_le_mul_right t (show j + 1 ≤ k by omega)
      rw [Nat.add_mul, one_mul] at this
      exact this
    refine kOutNK_of_sim hS' (by unfold aRB at hRB ⊢; omega)
      (by unfold aOUT at hOUT ⊢; omega) (hdist j hj i hi) fun z hz => ?_
    obtain ⟨hz0, hz1⟩ := odist_le_tripW H hz
    have h1' : ((z : ℤ) : ℝ) ≤ Hc := by
      have : ((z : ℤ) : ℝ) ≤ tripW S ℓ := by exact_mod_cast hz1
      linarith [tripW_le_kleinHI (V := V) (F := F) (S := S) (ℓ := ℓ) (k := k)]
    refine ⟨hz0, ?_⟩
    have h2' : z ≤ (Hc : ℤ) := by exact_mod_cast h1'
    omega
  · rw [hS'.output, ho]; rfl
  · -- the memory
    by_cases hw : a ≤ WK
    · rw [hS'.nmem a hw, h3 a ha]
      simp only [hc, liftK, hw, ↓reduceIte]
    · exact hfm a (by omega) (by omega)
  · rw [hS'.nmem a (by omega)]; exact h5 a ha
  · exact (hS'.rmem a ha).lt (by omega)

set_option maxHeartbeats 1000000 in
/-- **`klein_memN` with the read-back**: `kleinMemNDC` (Klein on natural words, then the `k t`
answer words divided by `N` with `divN` and cut off at `Wc`) from every natural configuration
holding the encoding, with words at most `WN` (`N, Wc ≤ WN`); the natural answers read at the end are
the distances divided by `N`, cut off at `Wc`. It keeps the natural registers `≥ 408`, the
natural memory above the work space outside `[βK, βK + WK]`, the reals and the output. -/
theorem klein_memNDC (H : Hyp M k g S ℓ) (hR : SameReach M k g S ℓ) {t : ℕ} {X : ℕ → V}
    {n B : ℕ} {σ : D ≃ Fin (Fintype.card D)} {Pk : Input}
    (hn : n = 2 * (Fintype.card V + Fintype.card F + Fintype.card D))
    (hv : KVal M k g S ℓ σ n B t X Pk) {Hc : ℕ} (hHc : kleinHI V F S ℓ k ≤ Hc)
    {β WK βK WN : ℕ} (hβK : WK < βK) (hWN : βK + WK + (2 * Hc + 1) * (2 * Hc + 1) + (2 * Hc + 1) ≤ WN)
    (N Wc : ℕ) (hNW : N ≤ WN) (hWcW : Wc ≤ WN) (P' : Input) (d : Config)
    (hd : WordsBounded WN d) (hr : ∀ r < 404, d.nreg r = 0)
    (hm : ∀ a ≤ WK, d.nmem a ≤ WK) (hlow : ∀ a ≤ B + 16 * (n + 1), d.nmem a ≤ B + 16 * (n + 1))
    (hE : KleinEncN M k g S ℓ σ B n β WK βK (2 * Hc + 1) Pk d) :
    ∃ d' steps,
      Exec P' WN (kleinMemNDC B (Fintype.card D) n k t β Pk.data.length Hc βK N Wc)
        d d' steps ∧
      steps ≤ 4 * (3 * (36500000 * ((Fintype.card V + Fintype.card F + Fintype.card D) *
          BKMNW.lg (Fintype.card V + Fintype.card F + Fintype.card D) +
        k * t * BKMNW.lg (Fintype.card V + Fintype.card F + Fintype.card D)))) +
          14 * (k * t) + 12 ∧
      (∀ j < k, ∀ i < t, kOutNK (Fintype.card D) n t βK d' j i =
        ((odist 𝒢 (tripSrc M k g j) (X i)).map (· / (N : ℤ))).bind (cutW (Wc : ℤ))) ∧
      d'.output = d.output ∧ (∀ r, 408 ≤ r → d'.nreg r = d.nreg r) ∧
      (∀ a, B + 16 * (n + 1) < a → (a ≤ WK ∨ (a < βK ∨ βK + WK < a)) → d'.nmem a = d.nmem a) ∧
      d'.rreg = d.rreg ∧ d'.rmem = d.rmem ∧
      (∀ a ≤ B + 16 * (n + 1), d'.nmem a ≤ B + 16 * (n + 1)) ∧
      (∀ a ≤ WK, d'.nmem (βK + a) < 2 * Hc + 1) := by
  obtain ⟨d₁, s₁, e₁, hs₁, hd₁, ho₁, hr₁, hm₁, hrr₁, hrm₁, hw₁, hres₁, hOUT, hRB⟩ :=
    klein_memN H hR hn hv hHc hβK hWN P' d hd hr hm hlow hE
  have hRB' : aRB n + k * t ≤ βK + aOUT (Fintype.card D) := by
    have := hE.dat.lt; have := hE.dat.le; omega
  obtain ⟨d', s₂, el, hs₂, hmc, ho, hrr, hrm⟩ := divCutLoop_exec (P := P')
    (base := βK + aOUT (Fintype.card D)) (rb := aRB n) (L := k * t) (N := N)
    (Wc := Wc) e₁.wb_right (by have := hE.dat.lt; have := hE.dat.le; unfold aOUT at hOUT ⊢; omega)
    hRB' (by omega) (by omega)
  have hRg : (divCutLoop (βK + aOUT (Fintype.card D)) (aRB n) (k * t) N Wc).regsOK
      (fun r => decide (r < 12)) = true := by kernel_rfl
  have hkeep := NegSSSP.exec_nreg_keep el hRg (by kernel_rfl) (by kernel_rfl)
  have hKw : B < B + 16 * (n + 1) := by omega
  refine ⟨d', s₁ + s₂, Exec.seq e₁ el, by omega, fun j hj i hi => ?_, by rw [ho, ho₁],
    fun r hr' => ?_, fun a ha ha' => ?_, by rw [hrr, hrr₁], by rw [hrm, hrm₁], fun a ha => ?_, fun a ha => ?_⟩
  · have hq : j * t + i < k * t := by
      have := Nat.mul_le_mul_right t (show j + 1 ≤ k by omega)
      rw [Nat.add_mul, one_mul] at this
      omega
    rw [kOutNK_divCutLoop hmc hq hRB', hd₁ j hj i hi]
  · rw [hkeep r (by simp; omega), hr₁ r hr']
  · rw [hmc a]
    unfold cutMem
    have hdl := hE.dat.lt
    have hdle := hE.dat.le
    have n1 : ¬ (βK + aOUT (Fintype.card D) ≤ a ∧
        a < βK + aOUT (Fintype.card D) + k * t) := by unfold aOUT at hOUT ⊢; omega
    have n2 : ¬ (aRB n ≤ a ∧ a < aRB n + k * t) := by unfold aRB at hRB ⊢; omega
    simp only [n1, n2, ↓reduceIte]
    exact hm₁ a ha ha'
  · rw [hmc a]
    unfold cutMem
    have hdl := hE.dat.lt
    have hdle := hE.dat.le
    have n1 : ¬ (βK + aOUT (Fintype.card D) ≤ a ∧
        a < βK + aOUT (Fintype.card D) + k * t) := by omega
    simp only [n1, ↓reduceIte]
    split_ifs <;> (try simp only [mul_one, mul_zero]) <;>
      first | exact hw₁ a ha | exact Nat.zero_le _
  · rw [hmc (βK + a)]
    unfold cutMem
    have hdl := hE.dat.lt
    have hdle := hE.dat.le
    have n2 : ¬ (aRB n ≤ βK + a ∧ βK + a < aRB n + k * t) := by unfold aRB at hRB ⊢; omega
    simp only [n2, ↓reduceIte]
    split_ifs
    · exact lt_of_le_of_lt (Nat.div_le_self _ _) (hres₁ a ha)
    · exact hres₁ a ha

end Klein

end PlanarFlow
