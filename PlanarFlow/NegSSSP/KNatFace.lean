module

public import PlanarFlow.NegSSSP.KNatMem
public import PlanarFlow.NegSSSP.KEncPert
public import PlanarFlow.NegSSSP.ReadMachNat

/-!
# A one-face instance on natural words with the isolating lengths, reading its encoding

The chain of `PlanarFlow/NegSSSP/KEncPert.lean` (`src_exec_valBy`, `faceInst_exec_valBy`,
`FEncValBy`, `fd_exec_valBy`) gives Klein's run at a node from any encoding of the lengths
**perturbed by `2^|D|`** (`MSSP.pertBy`), with real registers. Here the same chain is restated for
the **isolating lengths** `MSSP.isoLen` of Tewari–Vinodchandran (polynomial in the size of the
map, `PlanarFlow/MSSP/Isolate.lean`) **on natural words**, from every natural configuration
holding the encoding (`Klein.KleinEncN`):

* `Klein.src_memN`: on the map with the sources copied, for every isolating weight `w`
  (`MSSP.IsoW`, `|w| ≤ #F`) and the numbering `σ` of the encoding, the program
  `kleinMemNDC` (Klein on natural words reading its encoding from memory, then the answers
  divided by `N₁` with `divN` and cut off at `srcW`) leaves **the distances in the piece** in
  its natural answers (`kOutNK`).
* `NegSSSP.faceInst_memN`, `NegSSSP.FEncNat`, `NegSSSP.fd_memN`: on a one-face instance and at
  a node (`q ≤ 18 m`, `k² ≤ 1200 m`), within `12 · 32886 · 2372500000 · m lg m + 14 k² + 12`
  steps.
* `NegSSSP.fencNat_exists`: `FEncNat` is met by the explicit words `Klein.kInputT`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace Klein

open Finset CombMap MSSP STFlow DynTree WordRAM WordRAM.Machine WordRAM.Machine.Stmt

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F]

variable {M : CombMap D V F} {k : ℕ} {g : ℕ → D} {S : Finset D} {ℓ : D → ℤ}

/-- **The isolating lengths on the map with the sources copied**: `MSSP.isoLen` of the lengths
with the sources copied (`srcLen ℓ (srcW S ℓ)`), for the weight `w` and the numbering `σ`, with
`n = #V'`, `m = #D'`, `B = #F'` of that map. -/
def srcIso (k : ℕ) (S : Finset D) (ℓ : D → ℤ) (w : SrcD D k → ℤ)
    (σ : SrcD D k ≃ Fin (Fintype.card (SrcD D k))) : SrcD D k → ℤ :=
  isoLen (Fintype.card (SrcV V k)) (Fintype.card (SrcD D k)) (Fintype.card (SrcF F k)) w
    (fun d => (σ d : ℕ)) (srcLen ℓ (srcW S ℓ))

/-- `N₁` of the map with the sources copied. -/
def srcN1 (V F : Type*) [Fintype V] [Fintype F] (D : Type*) [Fintype D] (k : ℕ) : ℕ :=
  isoN1 (Fintype.card (SrcV V k)) (Fintype.card (SrcD D k)) (Fintype.card (SrcF F k))

section Src

variable (hf : FaceCycle M k g)

include hf in
/-- **The isolating lengths meet the article's hypotheses, and their distances divided by `N₁`
are those of the lengths with the sources copied.** -/
theorem srcIso_hyp (hM : M.IsPlane) (hrot : M.RotTrans) (hnn : ∀ d ∈ S, 0 ≤ ℓ d)
    {w : SrcD D k → ℤ} {f₀ : SrcF F k} (hw : IsoW (srcMap hf) f₀ w)
    (hwB : ∀ d, |w d| ≤ Fintype.card (SrcF F k))
    (σ : SrcD D k ≃ Fin (Fintype.card (SrcD D k))) :
    Hyp (srcMap hf) k (srcG hf) (srcPiece k S) (srcIso (V := V) (F := F) k S ℓ w σ) ∧
      ∀ x v, (odist (pieceGraph (srcMap hf) (srcPiece k S) (srcIso (V := V) (F := F) k S ℓ w σ))
        x v).map (· / (srcN1 V F D k : ℤ)) =
        odist (pieceGraph (srcMap hf) (srcPiece k S) (srcLen ℓ (srcW S ℓ))) x v := by
  have H0 := srcMap_hypNN hf hM hrot hnn (srcW_pos hnn).le
  have hι : Function.Injective fun d => (σ d : ℕ) := fun a b h => σ.injective (Fin.ext h)
  have hιm : ∀ d, (σ d : ℕ) < Fintype.card (SrcD D k) := fun d => (σ d).isLt
  exact ⟨H0.hypIso hw hwB le_rfl hι hιm, odist_isoLen hwB le_rfl hιm H0.nonneg⟩

include hf in
/-- **Klein's program on the map with the sources copied, on natural words, reading its
encoding from memory, on the isolating lengths** (see the module docstring). -/
theorem src_memN (hM : M.IsPlane) (hrot : M.RotTrans) (hnn : ∀ d ∈ S, 0 ≤ ℓ d) {t : ℕ}
    {X : ℕ → V} {n B : ℕ} {σ : SrcD D k ≃ Fin (Fintype.card (SrcD D k))} {Pk : Input}
    {w : SrcD D k → ℤ} {f₀ : SrcF F k} (hw : IsoW (srcMap hf) f₀ w)
    (hwB : ∀ d, |w d| ≤ Fintype.card (SrcF F k))
    (hn : n = 2 * (Fintype.card (SrcV V k) + Fintype.card (SrcF F k) + Fintype.card (SrcD D k)))
    (hv : KVal (srcMap hf) k (srcG hf) (srcPiece k S) (srcIso (V := V) (F := F) k S ℓ w σ) σ n B
      t (fun i => .inl (X i)) Pk)
    {Hc : ℕ} (hHc : kleinHI (SrcV V k) (SrcF F k) (srcPiece k S)
      (srcIso (V := V) (F := F) k S ℓ w σ) k ≤ Hc)
    {β WK βK WN : ℕ} (hβK : WK < βK)
    (hWN : βK + WK + (2 * Hc + 1) * (2 * Hc + 1) + (2 * Hc + 1) ≤ WN)
    (hNW : srcN1 V F D k ≤ WN) (hWcW : (srcW S ℓ).toNat ≤ WN)
    (P' : Input) (d : Config) (hd : WordsBounded WN d) (hr : ∀ r < 404, d.nreg r = 0)
    (hm : ∀ a ≤ WK, d.nmem a ≤ WK) (hlow : ∀ a ≤ B + 16 * (n + 1), d.nmem a ≤ B + 16 * (n + 1))
    (hE : KleinEncN (srcMap hf) k (srcG hf) (srcPiece k S) (srcIso (V := V) (F := F) k S ℓ w σ) σ
      B n β WK βK (2 * Hc + 1) Pk d) :
    ∃ d' steps,
      Exec P' WN
        (kleinMemNDC B (Fintype.card (SrcD D k)) n k t β Pk.data.length Hc βK (srcN1 V F D k)
          (srcW S ℓ).toNat) d d' steps ∧
      steps ≤ 12 * (2372500000 * ((Fintype.card V + Fintype.card F + Fintype.card D) *
          BKMNW.lg (Fintype.card V + Fintype.card F + Fintype.card D) +
        k * t * BKMNW.lg (Fintype.card V + Fintype.card F + Fintype.card D))) + 14 * (k * t) + 12 ∧
      (∀ j < k, ∀ i < t, kOutNK (Fintype.card (SrcD D k)) n t βK d' j i =
        odist (pieceGraph M S ℓ) (M.tail (g j)) (X i)) ∧
      d'.output = d.output ∧ (∀ r, 408 ≤ r → d'.nreg r = d.nreg r) ∧
      (∀ a, B + 16 * (n + 1) < a → (a ≤ WK ∨ (a < βK ∨ βK + WK < a)) → d'.nmem a = d.nmem a) ∧
      d'.rreg = d.rreg ∧ d'.rmem = d.rmem ∧
      (∀ a ≤ B + 16 * (n + 1), d'.nmem a ≤ B + 16 * (n + 1)) ∧
      (∀ a ≤ WK, d'.nmem (βK + a) < 2 * Hc + 1) := by
  obtain ⟨H, hdiv⟩ := srcIso_hyp hf hM hrot hnn hw hwB σ
  have hR := srcMap_sameReach hf (S := S) (srcIso (V := V) (F := F) k S ℓ w σ)
  obtain ⟨d', steps, ex, hs, hans, ho, h1, h2, h3, h4, h5, h6⟩ := klein_memNDC H hR hn hv hHc hβK hWN
    (srcN1 V F D k) (srcW S ℓ).toNat hNW hWcW P' d hd hr hm hlow hE
  have hcost : 36500000 * ((Fintype.card (SrcV V k) + Fintype.card (SrcF F k) +
      Fintype.card (SrcD D k)) * BKMNW.lg (Fintype.card (SrcV V k) + Fintype.card (SrcF F k) +
        Fintype.card (SrcD D k)) + k * t * BKMNW.lg (Fintype.card (SrcV V k) +
          Fintype.card (SrcF F k) + Fintype.card (SrcD D k))) ≤
      2372500000 * ((Fintype.card V + Fintype.card F + Fintype.card D) *
          BKMNW.lg (Fintype.card V + Fintype.card F + Fintype.card D) +
        k * t * BKMNW.lg (Fintype.card V + Fintype.card F + Fintype.card D)) := by
    set N := Fintype.card V + Fintype.card F + Fintype.card D with hN
    have hk : k ≤ Fintype.card V := by
      have hinj : Function.Injective fun i : Fin k => M.tail (g i) := fun i j h =>
        Fin.ext (hf.inj _ i.2 _ j.2 h)
      simpa using Fintype.card_le_of_injective _ hinj
    have hN1 : 1 ≤ N := by have := hf.two_le; omega
    have e : Fintype.card (SrcV V k) + Fintype.card (SrcF F k) + Fintype.card (SrcD D k) =
        N + 12 * k := by
      simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool,
        card_srcKind, hN]
      ring
    rw [e]
    have h13 : N + 12 * k ≤ 13 * N := by omega
    have hl : BKMNW.lg (N + 12 * k) ≤ 5 * BKMNW.lg N := by
      have h1 := BKMNW.lg_mono (show N + 12 * k ≤ 16 * N by omega)
      have h2 := lg_sixteen_mul hN1
      have h3 := BKMNW.one_le_lg N
      omega
    have h4 : (N + 12 * k) * BKMNW.lg (N + 12 * k) ≤ 13 * N * (5 * BKMNW.lg N) :=
      Nat.mul_le_mul h13 hl
    have h5 : k * t * BKMNW.lg (N + 12 * k) ≤ k * t * (5 * BKMNW.lg N) :=
      Nat.mul_le_mul_left _ hl
    have e4 : 13 * N * (5 * BKMNW.lg N) = 65 * (N * BKMNW.lg N) := by ring
    have e5 : k * t * (5 * BKMNW.lg N) = 5 * (k * t * BKMNW.lg N) := by ring
    omega
  refine ⟨d', steps, ex, ?_, fun j hj i hi => ?_, ho, h1, h2, h3, h4, h5, h6⟩
  · have := Nat.mul_le_mul_left 12 hcost
    omega
  · have e : tripSrc (srcMap hf) k (srcG hf) j = .inr (⟨j, hj⟩, false) := by
      unfold tripSrc; rw [Nat.mod_eq_of_lt hj]; exact srcTail_srcG hf hj
    rw [hans j hj i hi, hdiv, e, Int.toNat_of_nonneg (srcW_pos hnn).le]
    exact odist_src hf hnn ⟨j, hj⟩ (X i)

end Src

end Klein

namespace NegSSSP

open Finset BKMNW CombMap WordRAM WordRAM.Machine

universe u v w

variable {D : Type u} {V : Type v} {F : Type w} [Fintype D] [DecidableEq D] [Fintype V]
  [DecidableEq V] {N : CombMap D V F}

/-- **The encoding of a one-face instance for the isolating lengths**: `n` twice the size of
the map with the sources copied, an isolating weight `w` with the exceptional face of the first
source (`MSSP.IsoW`, `|w| ≤ #F'`), and `Klein.KVal` on the map with the sources copied for the
isolating lengths `srcIso` of the weight and the numbering `σ` of the encoding, the targets the
vertices `fd.Q.tail (fd.g i)`, `i < fd.k`. -/
def FEncNat {X : Finset D} {B : Finset V} (fd : FaceData N X B) (ℓ : D → ℤ) (n Bw : ℕ)
    (σ : Klein.SrcD fd.DQ fd.k ≃ Fin (Fintype.card (Klein.SrcD fd.DQ fd.k)))
    (w : Klein.SrcD fd.DQ fd.k → ℤ) (Pk : Input) : Prop :=
  n = 2 * (Fintype.card (Klein.SrcV fd.VQ fd.k) + Fintype.card (Klein.SrcF fd.FQ fd.k) +
      Fintype.card (Klein.SrcD fd.DQ fd.k)) ∧
    MSSP.IsoW (Klein.srcMap fd.inst.cycle)
      ((Klein.srcMap fd.inst.cycle).face (Klein.srcG fd.inst.cycle 0)) w ∧
    (∀ d, |w d| ≤ Fintype.card (Klein.SrcF fd.FQ fd.k)) ∧
    Klein.KVal (Klein.srcMap fd.inst.cycle) fd.k (Klein.srcG fd.inst.cycle)
      (Klein.srcPiece fd.k (fd.P'.image fd.e))
      (Klein.srcIso (V := fd.VQ) (F := fd.FQ) fd.k (fd.P'.image fd.e) (faceLen fd.P' fd.e ℓ) w σ)
      σ n Bw fd.k (fun i => .inl (fd.Q.tail (fd.g i))) Pk

/-- The bound `kleinHI` of the isolating lengths of an instance. -/
noncomputable def fdHI {X : Finset D} {B : Finset V} (fd : FaceData N X B) (ℓ : D → ℤ)
    (σ : Klein.SrcD fd.DQ fd.k ≃ Fin (Fintype.card (Klein.SrcD fd.DQ fd.k)))
    (w : Klein.SrcD fd.DQ fd.k → ℤ) : ℝ :=
  Klein.kleinHI (Klein.SrcV fd.VQ fd.k) (Klein.SrcF fd.FQ fd.k)
    (Klein.srcPiece fd.k (fd.P'.image fd.e))
    (Klein.srcIso (V := fd.VQ) (F := fd.FQ) fd.k (fd.P'.image fd.e) (faceLen fd.P' fd.e ℓ) w σ)
    fd.k

set_option maxHeartbeats 1000000 in
/-- **A one-face instance at a node, on natural words, reading its encoding** (`fd_exec_valBy`
on natural words with the isolating lengths): for a one-face instance `fd` of a part `X`
(`fd.q ≤ 18 m`, `fd.k² ≤ 1200 m`), the lengths `ℓ ≥ 0` on `X`, an encoding meeting `FEncNat`
and `Hc ≥ kleinHI` of its isolating lengths, from every natural configuration holding the
encoding (`Klein.KleinEncN`, residues modulo `2 Hc + 1`) with the registers `< 404` cleared, its
memory `≤ WK` bounded by `WK` and the work space bounded by its bound, `kleinMemNDC` runs within
`12 · 32886 · 2372500000 · m lg m + 14 k² + 12` steps, and for all shared vertices `b`, `b'` the
natural answer read at the end (`kOutNK`) is the distance in the piece `X` from `b` to `b'`. -/
theorem fd_memN {P P₀ P₁ X : Finset D} (fd : FaceData N X (bdry N P₀ P₁))
    (hq : fd.q ≤ 18 * P.card) (hk : fd.k ^ 2 ≤ 1200 * P.card) {ℓ : D → ℤ}
    (hnn : ∀ d ∈ X, 0 ≤ ℓ d) {n Bw : ℕ}
    {σ : Klein.SrcD fd.DQ fd.k ≃ Fin (Fintype.card (Klein.SrcD fd.DQ fd.k))}
    {w : Klein.SrcD fd.DQ fd.k → ℤ} {Pk : Input} (hv : FEncNat fd ℓ n Bw σ w Pk)
    {Hc : ℕ} (hHc : fdHI fd ℓ σ w ≤ Hc)
    {β WK βK WN : ℕ} (hβK : WK < βK)
    (hWN : βK + WK + (2 * Hc + 1) * (2 * Hc + 1) + (2 * Hc + 1) ≤ WN)
    (hNW : Klein.srcN1 fd.VQ fd.FQ fd.DQ fd.k ≤ WN)
    (hWcW : (Klein.srcW (fd.P'.image fd.e) (faceLen fd.P' fd.e ℓ)).toNat ≤ WN)
    (P'' : Input) (d : Config) (hd : WordsBounded WN d) (hr : ∀ r < 404, d.nreg r = 0)
    (hm : ∀ a ≤ WK, d.nmem a ≤ WK)
    (hlow : ∀ a ≤ Bw + 16 * (n + 1), d.nmem a ≤ Bw + 16 * (n + 1))
    (hE : Klein.KleinEncN (Klein.srcMap fd.inst.cycle) fd.k (Klein.srcG fd.inst.cycle)
      (Klein.srcPiece fd.k (fd.P'.image fd.e))
      (Klein.srcIso (V := fd.VQ) (F := fd.FQ) fd.k (fd.P'.image fd.e) (faceLen fd.P' fd.e ℓ) w σ)
      σ Bw n β WK βK (2 * Hc + 1) Pk d) :
    ∃ d' steps,
      Exec P'' WN
        (Klein.kleinMemNDC Bw (Fintype.card (Klein.SrcD fd.DQ fd.k)) n fd.k fd.k β
          Pk.data.length Hc βK (Klein.srcN1 fd.VQ fd.FQ fd.DQ fd.k)
          (Klein.srcW (fd.P'.image fd.e) (faceLen fd.P' fd.e ℓ)).toNat) d d' steps ∧
      steps ≤ 12 * (32886 * 2372500000 * P.card * lg P.card) + 14 * (fd.k * fd.k) + 12 ∧
      (∀ b ∈ bdry N P₀ P₁, ∃ i < fd.k, fd.Q.tail (fd.g i) = fd.j b ∧
        ∀ b' ∈ bdry N P₀ P₁, ∃ i' < fd.k, fd.Q.tail (fd.g i') = fd.j b' ∧
          Klein.kOutNK (Fintype.card (Klein.SrcD fd.DQ fd.k)) n fd.k βK d' i i' =
            MSSP.odist (MSSP.pieceGraph N X ℓ) b b') ∧
      d'.output = d.output ∧ (∀ r, 408 ≤ r → d'.nreg r = d.nreg r) ∧
      (∀ a, Bw + 16 * (n + 1) < a → (a ≤ WK ∨ (a < βK ∨ βK + WK < a)) → d'.nmem a = d.nmem a) ∧
      d'.rreg = d.rreg ∧ d'.rmem = d.rmem ∧
      (∀ a ≤ Bw + 16 * (n + 1), d'.nmem a ≤ Bw + 16 * (n + 1)) ∧
      (∀ a ≤ WK, d'.nmem (βK + a) < 2 * Hc + 1) := by
  obtain ⟨hn, hw, hwB, hv'⟩ := hv
  have h := fd.inst
  have hnnQ : ∀ y ∈ fd.P'.image fd.e, 0 ≤ faceLen fd.P' fd.e ℓ y := fun y _ =>
    faceLen_nonneg _ _ _ y
  obtain ⟨d', steps, ex, hs, hans, ho, h1, h2, h3, h4, h5, h6⟩ :=
    Klein.src_memN h.cycle h.plane h.rot hnnQ hw hwB hn hv' hHc hβK hWN hNW hWcW P'' d hd hr hm
      hlow hE
  have hℓ : ∀ d ∈ fd.P', faceLen fd.P' fd.e ℓ (fd.e d) = ℓ d := fun d hd =>
    faceLen_e h.injE (fun d' hd' => hnn d' (h.sub hd')) hd
  have hc1 : 2372500000 * ((Fintype.card fd.VQ + Fintype.card fd.FQ + Fintype.card fd.DQ) *
        lg (Fintype.card fd.VQ + Fintype.card fd.FQ + Fintype.card fd.DQ) +
      fd.k * fd.k * lg (Fintype.card fd.VQ + Fintype.card fd.FQ + Fintype.card fd.DQ)) ≤
      2372500000 * (fd.q * lg fd.q + fd.k ^ 2 * lg fd.q) := by
    have hN := h.card
    have hl := lg_mono hN
    have h1 : (Fintype.card fd.VQ + Fintype.card fd.FQ + Fintype.card fd.DQ) *
        lg (Fintype.card fd.VQ + Fintype.card fd.FQ + Fintype.card fd.DQ) ≤ fd.q * lg fd.q :=
      Nat.mul_le_mul hN hl
    have h2 : fd.k * fd.k * lg (Fintype.card fd.VQ + Fintype.card fd.FQ + Fintype.card fd.DQ) ≤
        fd.k ^ 2 * lg fd.q := by
      rw [← sq]; exact Nat.mul_le_mul_left _ hl
    exact Nat.mul_le_mul_left _ (Nat.add_le_add h1 h2)
  have hc2 : 2372500000 * (fd.q * lg fd.q + fd.k ^ 2 * lg fd.q) ≤
      32886 * 2372500000 * P.card * lg P.card :=
    oneFace_cost_le (f := fun q k => 2372500000 * (q * lg q + k ^ 2 * lg q))
      (fun _ _ => le_rfl) hq hk
  refine ⟨d', steps, ex, ?_, fun b hb => ?_, ho, h1, h2, h3, h4, h5, h6⟩
  · have := Nat.mul_le_mul_left 12 (hc1.trans hc2)
    omega
  · obtain ⟨i, hi, hib⟩ := h.src b hb
    have hD := h.isDist hℓ hb (isDist_odist (fun a => faceLen_nonneg _ _ _ a.1) _)
    have hE' := odist_eq_of_isDist (fun a => hnn a.1 a.2) hD
    refine ⟨i, hi, hib, fun b' hb' => ?_⟩
    obtain ⟨i', hi', hib'⟩ := h.src b' hb'
    refine ⟨i', hi', hib', ?_⟩
    rw [hans i hi i' hi', hib, hib', ← hE']
    simp [hb']

/-- **`FEncNat` can be met, by the explicit words**: for every one-face instance `fd`, lengths
`ℓ ≥ 0` on the image of the piece and numbering `σ`, some isolating weight `w` and the words
`Klein.kInputT` of the map with the sources copied for its isolating lengths meet `FEncNat`. -/
theorem fencNat_exists {X : Finset D} {B : Finset V} (fd : FaceData N X B) (ℓ : D → ℤ)
    (σ : Klein.SrcD fd.DQ fd.k ≃ Fin (Fintype.card (Klein.SrcD fd.DQ fd.k))) :
    ∃ (n Bw : ℕ) (w : Klein.SrcD fd.DQ fd.k → ℤ) (Pk : Input), FEncNat fd ℓ n Bw σ w Pk := by
  classical
  have hnnQ : ∀ y ∈ fd.P'.image fd.e, 0 ≤ faceLen fd.P' fd.e ℓ y := fun y _ =>
    faceLen_nonneg _ _ _ y
  obtain ⟨w, hw, hwB⟩ := MSSP.exists_isoW (Klein.srcMap_isPlane fd.inst.cycle fd.inst.plane)
    ((Klein.srcMap fd.inst.cycle).face (Klein.srcG fd.inst.cycle 0))
  obtain ⟨H, -⟩ := Klein.srcIso_hyp fd.inst.cycle fd.inst.plane fd.inst.rot hnnQ hw hwB σ
  have hR := Klein.srcMap_sameReach fd.inst.cycle (S := fd.P'.image fd.e)
    (Klein.srcIso (V := fd.VQ) (F := fd.FQ) fd.k (fd.P'.image fd.e) (faceLen fd.P' fd.e ℓ) w σ)
  have hX : ∀ i < fd.k, ¬ MSSP.IsRoot (Klein.srcMap fd.inst.cycle) fd.k
      (Klein.srcG fd.inst.cycle) (.inl (fd.Q.tail (fd.g i))) := by
    rintro i - ⟨j, hj, hji⟩
    rw [Klein.srcTail_srcG fd.inst.cycle hj] at hji
    cases hji
  obtain ⟨ιv, ιg, ιf, ιe, hL⟩ := Klein.exists_layout (Klein.srcMap fd.inst.cycle)
  obtain ⟨T, C, vs, ts, fs, cs, hOT, hOC, hoff, hCr, hT⟩ := Klein.klein_init_exists H hR
  exact ⟨_, _, w, _, rfl, hw, hwB, Klein.kval_kInputT H hX σ hL hOT hOC hoff hCr hT⟩

end NegSSSP

end PlanarFlow
