module

public import PlanarFlow.NegSSSP.FaceKlein
public import PlanarFlow.Klein.ExecEnc

/-!
# Klein's program at a node from the encoding of the one-face instance in memory

`PlanarFlow.NegSSSP.splitF_exec` runs `kleinProg` on the one-face instance of a part of a node
(the map with the sources copied, `PlanarFlow.Klein.srcMap`) **from a starting configuration
built inside its proof**. Here the same calls start from **any** configuration holding the
encoding of that instance in memory (`PlanarFlow.Klein.KleinEnc`: the input words at a base `β`
above the work space, and the real constants), by `PlanarFlow.Klein.klein_exec_enc_exists`
(the program `kleinProgMem` reads its input words from memory), so that the call can be one
step of a longer run:

* `Klein.src_exec_enc`: `Klein.src_exec` from the encoding, within three times its bound.
* `faceInst_exec_enc`: `faceInst_exec` from the encoding.
* `splitF_exec_enc`: **`splitF_exec` from the encoding**: at a node meeting `SplitF`, for each
  part there are a one-face instance `fd : FaceData`, sizes `n`, `Bw`, a numbering `σ` of the
  darts of the map with the sources copied and input words `Pk` (the encoding, `kInputT` of the
  instance) such that from every configuration `d` holding `KleinEnc` of the instance at a base
  `β` (registers `< 201` and memory `≤ Bw + 16 (n + 1)` bounded by `Bw + 16 (n + 1)`),
  `kleinProgMem` runs within `3 · 32886 · 2372500000 · m lg m` steps to the distances in the
  part between the shared vertices (read back by `Klein.srcOut`), keeping the output, the
  registers above `201` and the memory above `Bw + 16 (n + 1)`, and leaving the natural memory
  `≤ Bw + 16 (n + 1)` bounded by `Bw + 16 (n + 1)`; the size bound of the instance is
  `fd.q = 18 m`.

The instance is the one of `SplitF` (chosen by `OneFace`, an existence statement): its encoding
is an **input** of the run (the hypothesis `KleinEnc … d`), not computed from the plain encoding
of the node; constructing it is the glue of the separator (the corners of the instance), not
realized.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace Klein

open Finset CombMap MSSP WordRAM WordRAM.Machine

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F] {M : CombMap D V F} {k : ℕ} {g : ℕ → D}
  (hf : FaceCycle M k g) {S : Finset D} {ℓ : D → ℤ}

include hf in
/-- **Klein's program on the map with the sources copied, from the encoding in memory** (see
the module docstring). -/
theorem src_exec_enc (hM : M.IsPlane) (hrot : M.RotTrans) (hnn : ∀ d ∈ S, 0 ≤ ℓ d) (t : ℕ)
    (X : ℕ → V) :
    ∃ (n B : ℕ) (σ : SrcD D k ≃ Fin (Fintype.card (SrcD D k))) (Pk : Input),
      n = 2 * (Fintype.card (SrcV V k) + Fintype.card (SrcF F k) + Fintype.card (SrcD D k)) ∧
      ∀ (P' : Input) (W' β : ℕ) (d : Config), WordsBounded W' d →
        (∀ r < 201, d.nreg r ≤ B + 16 * (n + 1)) →
        (∀ a ≤ B + 16 * (n + 1), d.nmem a ≤ B + 16 * (n + 1)) →
        KleinEnc (srcMap hf) k (srcG hf) (srcPiece k S) (pert (srcLen ℓ (srcW S ℓ))) σ B n β W'
          Pk d →
        ∃ d' steps,
          Exec P' W' (kleinProgMem B (Fintype.card (SrcD D k)) n k t β Pk.data.length) d d'
            steps ∧
          steps ≤ 3 * (2372500000 * ((Fintype.card V + Fintype.card F + Fintype.card D) *
              BKMNW.lg (Fintype.card V + Fintype.card F + Fintype.card D) +
            k * t * BKMNW.lg (Fintype.card V + Fintype.card F + Fintype.card D))) ∧
          (∀ j < k, ∀ i < t, srcOut (srcW S ℓ) (Fintype.card (SrcD D k))
            (kOut (Fintype.card (SrcD D k)) n t d' j i) =
              odist (pieceGraph M S ℓ) (M.tail (g j)) (X i)) ∧
          d'.output = d.output ∧ (∀ r, 201 < r → d'.nreg r = d.nreg r) ∧
          (∀ r, 201 ≤ r → d'.rreg r = d.rreg r) ∧
          (∀ a, B + 16 * (n + 1) < a → d'.nmem a = d.nmem a) ∧
          (∀ a, B + 16 * (n + 1) < a → d'.rmem a = d.rmem a) ∧
          (∀ a ≤ B + 16 * (n + 1), d'.nmem a ≤ B + 16 * (n + 1)) := by
  have H := (srcMap_hypNN hf hM hrot hnn (srcW_pos hnn).le).hyp
  have hR := srcMap_sameReach hf (S := S) (pert (srcLen ℓ (srcW S ℓ)))
  have hX : ∀ i < t, ¬ IsRoot (srcMap hf) k (srcG hf) (.inl (X i)) := by
    rintro i - ⟨j, hj, hji⟩
    rw [srcTail_srcG hf hj] at hji
    cases hji
  obtain ⟨n, B, σ, Pk, hn, hrun⟩ := klein_exec_enc_exists H hR t (fun i => .inl (X i)) hX
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
  refine ⟨n, B, σ, Pk, hn, fun P' W' β d hd hrb hmb hE => ?_⟩
  obtain ⟨d', steps, ex, hs, -, hdist, ho, h1, h2, h3, h4⟩ := hrun P' W' β d hd hrb hmb hE
  refine ⟨d', steps, ex, hs.trans (Nat.mul_le_mul_left 3 hcost), fun j hj i hi => ?_, ho, h1,
    h2, h3, h4⟩
  rw [hdist j hj i hi, ← srcAns_eq hf hM hrot hnn hj]
  unfold srcOut srcAns kleinNN
  rw [outNN_map, ← kleinAns_eq H hR]

end Klein

namespace NegSSSP

open Finset BKMNW CombMap WordRAM WordRAM.Machine

universe u v w

variable {D : Type u} {V : Type v} {F : Type w} [Fintype D] [DecidableEq D] [Fintype V]
  [DecidableEq V] {N : CombMap D V F}

variable {P : Finset D} {B : Finset V} {q k : ℕ} {DQ VQ FQ : Type u} [Fintype DQ]
  [DecidableEq DQ] [Fintype VQ] [DecidableEq VQ] [Fintype FQ] [DecidableEq FQ]
  {Q : CombMap DQ VQ FQ} {g : ℕ → DQ} {P' : Finset D} {e : D → DQ} {j : V → VQ}

/-- **Klein's program on a one-face instance, from the encoding in memory.** -/
theorem faceInst_exec_enc (h : FaceInst N P B q k Q g P' e j) {ℓ : D → ℤ}
    (hnn : ∀ d ∈ P, 0 ≤ ℓ d) :
    ∃ (n Bw : ℕ) (σ : Klein.SrcD DQ k ≃ Fin (Fintype.card (Klein.SrcD DQ k))) (Pk : Input),
      ∀ (P'' : Input) (W' β : ℕ) (d : Config), WordsBounded W' d →
        (∀ r < 201, d.nreg r ≤ Bw + 16 * (n + 1)) →
        (∀ a ≤ Bw + 16 * (n + 1), d.nmem a ≤ Bw + 16 * (n + 1)) →
        Klein.KleinEnc (Klein.srcMap h.cycle) k (Klein.srcG h.cycle)
          (Klein.srcPiece k (P'.image e))
          (MSSP.pert (Klein.srcLen (faceLen P' e ℓ) (Klein.srcW (P'.image e) (faceLen P' e ℓ))))
          σ Bw n β W' Pk d →
        ∃ d' steps,
          Exec P'' W' (Klein.kleinProgMem Bw (Fintype.card (Klein.SrcD DQ k)) n k k β
            Pk.data.length) d d' steps ∧
          steps ≤ 3 * (2372500000 * (q * lg q + k ^ 2 * lg q)) ∧
          (∀ b ∈ B, ∃ i < k, Q.tail (g i) = j b ∧ ∀ b' ∈ B, ∃ i' < k, Q.tail (g i') = j b' ∧
            Klein.srcOut (Klein.srcW (P'.image e) (faceLen P' e ℓ))
              (Fintype.card (Klein.SrcD DQ k))
              (Klein.kOut (Fintype.card (Klein.SrcD DQ k)) n k d' i i') =
              MSSP.odist (MSSP.pieceGraph N P ℓ) b b') ∧
          d'.output = d.output ∧ (∀ r, 201 < r → d'.nreg r = d.nreg r) ∧
          (∀ r, 201 ≤ r → d'.rreg r = d.rreg r) ∧
          (∀ a, Bw + 16 * (n + 1) < a → d'.nmem a = d.nmem a) ∧
          (∀ a, Bw + 16 * (n + 1) < a → d'.rmem a = d.rmem a) ∧
          (∀ a ≤ Bw + 16 * (n + 1), d'.nmem a ≤ Bw + 16 * (n + 1)) := by
  have hnnQ : ∀ y ∈ P'.image e, 0 ≤ faceLen P' e ℓ y := fun y _ => faceLen_nonneg _ _ _ y
  obtain ⟨n, Bw, σ, Pk, -, hrun⟩ :=
    Klein.src_exec_enc h.cycle h.plane h.rot hnnQ k fun i => Q.tail (g i)
  have hℓ : ∀ d ∈ P', faceLen P' e ℓ (e d) = ℓ d := fun d hd =>
    faceLen_e h.injE (fun d' hd' => hnn d' (h.sub hd')) hd
  have hcost : 2372500000 * ((Fintype.card VQ + Fintype.card FQ + Fintype.card DQ) *
        lg (Fintype.card VQ + Fintype.card FQ + Fintype.card DQ) +
      k * k * lg (Fintype.card VQ + Fintype.card FQ + Fintype.card DQ)) ≤
      2372500000 * (q * lg q + k ^ 2 * lg q) := by
    have hN := h.card
    have hl := lg_mono hN
    have h1 : (Fintype.card VQ + Fintype.card FQ + Fintype.card DQ) *
        lg (Fintype.card VQ + Fintype.card FQ + Fintype.card DQ) ≤ q * lg q :=
      Nat.mul_le_mul hN hl
    have h2 : k * k * lg (Fintype.card VQ + Fintype.card FQ + Fintype.card DQ) ≤
        k ^ 2 * lg q := by
      rw [← sq]; exact Nat.mul_le_mul_left _ hl
    exact Nat.mul_le_mul_left _ (Nat.add_le_add h1 h2)
  refine ⟨n, Bw, σ, Pk, fun P'' W' β d hd hrb hmb hE => ?_⟩
  obtain ⟨d', steps, ex, hs, hdist, ho, h1, h2, h3, h4⟩ := hrun P'' W' β d hd hrb hmb hE
  refine ⟨d', steps, ex, hs.trans (Nat.mul_le_mul_left 3 hcost), fun b hb => ?_, ho, h1, h2, h3,
    h4⟩
  obtain ⟨i, hi, hib⟩ := h.src b hb
  have hD := h.isDist hℓ hb (isDist_odist (fun a => faceLen_nonneg _ _ _ a.1) _)
  have hE' := odist_eq_of_isDist (fun a => hnn a.1 a.2) hD
  refine ⟨i, hi, hib, fun b' hb' => ?_⟩
  obtain ⟨i', hi', hib'⟩ := h.src b' hb'
  refine ⟨i', hi', hib', ?_⟩
  rw [hdist i hi i' hi', hib, hib', ← hE']
  simp [hb']

/-- **Klein's program at a node of the decomposition by simple cycles, from the encoding of the
one-face instance in memory** (see the module docstring). -/
theorem splitF_exec_enc {P P₀ P₁ : Finset D} (h : SplitF N P P₀ P₁)
    (hB : (bdry N P₀ P₁).Nonempty) {ℓ : D → ℤ} {X : Finset D} (hX : X = P₀ ∨ X = P₁)
    (hnn : ∀ d ∈ X, 0 ≤ ℓ d) :
    ∃ fd : FaceData N X (bdry N P₀ P₁), ∃ (n Bw : ℕ)
      (σ : Klein.SrcD fd.DQ fd.k ≃ Fin (Fintype.card (Klein.SrcD fd.DQ fd.k))) (Pk : Input),
      fd.q = 18 * P.card ∧
      ∀ (P'' : Input) (W' β : ℕ) (d : Config), WordsBounded W' d →
        (∀ r < 201, d.nreg r ≤ Bw + 16 * (n + 1)) →
        (∀ a ≤ Bw + 16 * (n + 1), d.nmem a ≤ Bw + 16 * (n + 1)) →
        Klein.KleinEnc (Klein.srcMap fd.inst.cycle) fd.k (Klein.srcG fd.inst.cycle)
          (Klein.srcPiece fd.k (fd.P'.image fd.e))
          (MSSP.pert (Klein.srcLen (faceLen fd.P' fd.e ℓ)
            (Klein.srcW (fd.P'.image fd.e) (faceLen fd.P' fd.e ℓ)))) σ Bw n β W' Pk d →
        ∃ d' steps,
          Exec P'' W' (Klein.kleinProgMem Bw (Fintype.card (Klein.SrcD fd.DQ fd.k)) n fd.k fd.k
            β Pk.data.length) d d' steps ∧
          steps ≤ 3 * (32886 * 2372500000 * P.card * lg P.card) ∧
          (∀ b ∈ bdry N P₀ P₁, ∃ i < fd.k, fd.Q.tail (fd.g i) = fd.j b ∧
            ∀ b' ∈ bdry N P₀ P₁, ∃ i' < fd.k, fd.Q.tail (fd.g i') = fd.j b' ∧
              Klein.srcOut (Klein.srcW (fd.P'.image fd.e) (faceLen fd.P' fd.e ℓ))
                (Fintype.card (Klein.SrcD fd.DQ fd.k))
                (Klein.kOut (Fintype.card (Klein.SrcD fd.DQ fd.k)) n fd.k d' i i') =
              MSSP.odist (MSSP.pieceGraph N X ℓ) b b') ∧
          d'.output = d.output ∧ (∀ r, 201 < r → d'.nreg r = d.nreg r) ∧
          (∀ r, 201 ≤ r → d'.rreg r = d.rreg r) ∧
          (∀ a, Bw + 16 * (n + 1) < a → d'.nmem a = d.nmem a) ∧
          (∀ a, Bw + 16 * (n + 1) < a → d'.rmem a = d.rmem a) ∧
          (∀ a ≤ Bw + 16 * (n + 1), d'.nmem a ≤ Bw + 16 * (n + 1)) := by
  have h' := h
  obtain ⟨-, -, -, -, -, -, -, -, hw⟩ := h'
  obtain ⟨k, hk, h₀, h₁⟩ := hw hB
  have hX' : OneFace N X (bdry N P₀ P₁) (18 * P.card) k := by
    rcases hX with rfl | rfl
    · exact h₀
    · exact h₁
  obtain ⟨DQ, VQ, FQ, i1, i2, i3, i4, i5, i6, Q, g, P', e, j, hI⟩ := hX'
  obtain ⟨n, Bw, σ, Pk, hrun⟩ := faceInst_exec_enc hI hnn
  have hc : 2372500000 * (18 * P.card * lg (18 * P.card) + k ^ 2 * lg (18 * P.card)) ≤
      32886 * 2372500000 * P.card * lg P.card :=
    oneFace_cost_le (f := fun q k => 2372500000 * (q * lg q + k ^ 2 * lg q))
      (fun _ _ => le_rfl) le_rfl hk
  refine ⟨⟨18 * P.card, k, DQ, VQ, FQ, Q, g, P', e, j, hI⟩, n, Bw, σ, Pk, rfl,
    fun P'' W' β d hd hrb hmb hE => ?_⟩
  obtain ⟨d', steps, ex, hs, hR, ho, h1, h2, h3, h4⟩ := hrun P'' W' β d hd hrb hmb hE
  exact ⟨d', steps, ex, hs.trans (Nat.mul_le_mul_left 3 hc), hR, ho, h1, h2, h3, h4⟩

end NegSSSP

end PlanarFlow
