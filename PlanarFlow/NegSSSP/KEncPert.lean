module

public import PlanarFlow.NegSSSP.KEncVal

/-!
# The encoding of a one-face instance with an explicit perturbation

The lengths given to Klein's program on a one-face instance are the perturbed lengths
`MSSP.pert ℓ d = 2^|D| ℓ d + 2^(Fintype.equivFin D d)`, whose numbering of the darts is
`Fintype.equivFin` (chosen, not computable): no program can write the length words of that
encoding. Here the perturbation uses the numbering `σ` of the darts of the encoding itself:

* `MSSP.pertBy σ ℓ d = 2^|D| ℓ d + 2^(σ d)`; `MSSP.isPerturb_pertBy`, `MSSP.HypNN.hypBy`: it is
  a perturbation and meets the article's hypotheses; `MSSP.odist_pertBy`: the distances for
  `pertBy σ ℓ`, divided by `2^|D|`, are those for `ℓ`.
* `Klein.src_exec_valBy`, `NegSSSP.faceInst_exec_valBy`, `NegSSSP.FEncValBy`,
  `NegSSSP.fd_exec_valBy`, `NegSSSP.KPartRunBy`, `NegSSSP.kpart_exec_valBy`,
  `NegSSSP.kpair_execBy`: the chain of `PlanarFlow/NegSSSP/KEncVal.lean` (and `kpair_exec`) with
  `pertBy σ`; `NegSSSP.fencValBy_exists`: `FEncValBy` is met by the explicit words
  `Klein.kInputT` for every numbering `σ`.
* `NegSSSP.node_exec_valBy`: **the whole node as one run** (`node_exec`) for any instances of
  the two parts and any encodings meeting `FEncValBy` (the slots `KSlot` holding the encoding
  for the lengths perturbed by the numbering `σ` of the encoding).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace MSSP

open Finset

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F]

/-- **The perturbed lengths by a numbering `σ` of the darts**: `2^|D| · ℓ d + 2^(σ d)`. -/
def pertBy (σ : D ≃ Fin (Fintype.card D)) (ℓ : D → ℤ) (d : D) : ℤ :=
  2 ^ Fintype.card D * ℓ d + 2 ^ (σ d : ℕ)

variable {M : CombMap D V F} {k : ℕ} {g : ℕ → D} {S : Finset D} {ℓ : D → ℤ}

lemma isPerturb_pertBy (M : CombMap D V F) (S : Finset D) (ℓ : D → ℤ)
    (σ : D ≃ Fin (Fintype.card D)) :
    IsPerturb (pieceGraph M S ℓ) (pieceGraph M S (pertBy σ ℓ)) (fun a => (σ a.1 : ℕ))
      (Fintype.card D) where
  src := rfl
  dst := rfl
  len _ := rfl
  inj _ _ h := Subtype.ext (σ.injective (Fin.ext h))
  lt a := (σ a.1).isLt

/-- **The lengths perturbed by `σ` meet the article's assumptions.** -/
theorem HypNN.hypBy (H : HypNN M k g S ℓ) (σ : D ≃ Fin (Fintype.card D)) :
    Hyp M k g S (pertBy σ ℓ) where
  plane := H.plane
  rot := H.rot
  face := H.face
  pos d hd := (isPerturb_pertBy M S ℓ σ).pos (fun a => H.nonneg a.1 a.2) ⟨d, hd⟩
  noIn := H.noIn
  uniq := (isPerturb_pertBy M S ℓ σ).uniqTight (fun a => H.nonneg a.1 a.2)

/-- **The distances for the lengths perturbed by `σ`**, divided by `2^|D|`, are the distances
for the lengths. -/
theorem odist_pertBy (hnn : ∀ d ∈ S, 0 ≤ ℓ d) (σ : D ≃ Fin (Fintype.card D)) (x v : V) :
    (odist (pieceGraph M S (pertBy σ ℓ)) x v).map (· / 2 ^ Fintype.card D) =
      odist (pieceGraph M S ℓ) x v := by
  have hP := isPerturb_pertBy M S ℓ σ
  have hn : ∀ a : {d // d ∈ S}, 0 ≤ (pieceGraph M S ℓ).len a := fun a => hnn a.1 a.2
  unfold odist
  split_ifs with h1 h2 h2
  · rw [Option.map_some, ← hP.dist_div hn h2]
  · exact absurd (hP.reach_iff.1 h1) h2
  · exact absurd (hP.reach_iff.2 h2) h1
  · rfl

end MSSP

namespace Klein

open Finset CombMap MSSP STFlow DynTree WordRAM WordRAM.Machine WordRAM.Machine.Stmt

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F]

variable {M : CombMap D V F} {k : ℕ} {g : ℕ → D} {S : Finset D} {ℓ : D → ℤ}

section Src

variable (hf : FaceCycle M k g)

include hf in
/-- **`src_exec_val` with the perturbation by the numbering `σ` of the encoding**
(`MSSP.pertBy σ`, in place of `MSSP.pert`, which uses `Fintype.equivFin`). -/
theorem src_exec_valBy (hM : M.IsPlane) (hrot : M.RotTrans) (hnn : ∀ d ∈ S, 0 ≤ ℓ d) {t : ℕ}
    {X : ℕ → V} {n B : ℕ} {σ : SrcD D k ≃ Fin (Fintype.card (SrcD D k))} {Pk : Input}
    (hn : n = 2 * (Fintype.card (SrcV V k) + Fintype.card (SrcF F k) + Fintype.card (SrcD D k)))
    (hv : KVal (srcMap hf) k (srcG hf) (srcPiece k S) (pertBy σ (srcLen ℓ (srcW S ℓ))) σ n B t
      (fun i => .inl (X i)) Pk) :
      ∀ (P' : Input) (W' β : ℕ) (d : Config), WordsBounded W' d →
        (∀ r < 201, d.nreg r ≤ B + 16 * (n + 1)) →
        (∀ a ≤ B + 16 * (n + 1), d.nmem a ≤ B + 16 * (n + 1)) →
        KleinEnc (srcMap hf) k (srcG hf) (srcPiece k S) (pertBy σ (srcLen ℓ (srcW S ℓ))) σ B n β W'
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
  have HN := srcMap_hypNN hf hM hrot hnn (srcW_pos hnn).le
  have H := HN.hypBy σ
  have hR := srcMap_sameReach hf (S := S) (pertBy σ (srcLen ℓ (srcW S ℓ)))
  have hrun := klein_exec_val H hR hn hv
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
  intro P' W' β d hd hrb hmb hE
  obtain ⟨d', steps, ex, hs, -, hdist, ho, h1, h2, h3, h4⟩ := hrun P' W' β d hd hrb hmb hE
  refine ⟨d', steps, ex, hs.trans (Nat.mul_le_mul_left 3 hcost), fun j hj i hi => ?_, ho, h1,
    h2, h3, h4⟩
  rw [hdist j hj i hi]
  unfold srcOut
  rw [outNN_map, odist_pertBy HN.nonneg σ]
  have e : tripSrc (srcMap hf) k (srcG hf) j = .inr (⟨j, hj⟩, false) := by
    unfold tripSrc; rw [Nat.mod_eq_of_lt hj]; exact srcTail_srcG hf hj
  rw [e]
  exact odist_src hf hnn ⟨j, hj⟩ (X i)

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

/-- **`faceInst_exec_val` with the perturbation `MSSP.pertBy σ`** (on the map with the sources
copied, the lengths of the instance, the targets the vertices of the face). -/
theorem faceInst_exec_valBy (h : FaceInst N P B q k Q g P' e j) {ℓ : D → ℤ}
    (hnn : ∀ d ∈ P, 0 ≤ ℓ d) {n Bw : ℕ}
    {σ : Klein.SrcD DQ k ≃ Fin (Fintype.card (Klein.SrcD DQ k))} {Pk : Input}
    (hn : n = 2 * (Fintype.card (Klein.SrcV VQ k) + Fintype.card (Klein.SrcF FQ k) +
      Fintype.card (Klein.SrcD DQ k)))
    (hv : Klein.KVal (Klein.srcMap h.cycle) k (Klein.srcG h.cycle) (Klein.srcPiece k (P'.image e))
      (MSSP.pertBy σ (Klein.srcLen (faceLen P' e ℓ) (Klein.srcW (P'.image e) (faceLen P' e ℓ))))
      σ n Bw k (fun i => .inl (Q.tail (g i))) Pk) :
      ∀ (P'' : Input) (W' β : ℕ) (d : Config), WordsBounded W' d →
        (∀ r < 201, d.nreg r ≤ Bw + 16 * (n + 1)) →
        (∀ a ≤ Bw + 16 * (n + 1), d.nmem a ≤ Bw + 16 * (n + 1)) →
        Klein.KleinEnc (Klein.srcMap h.cycle) k (Klein.srcG h.cycle)
          (Klein.srcPiece k (P'.image e))
          (MSSP.pertBy σ (Klein.srcLen (faceLen P' e ℓ) (Klein.srcW (P'.image e) (faceLen P' e ℓ))))
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
  have hrun := Klein.src_exec_valBy h.cycle h.plane h.rot hnnQ hn hv
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
  intro P'' W' β d hd hrb hmb hE
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

/-- **`FEncVal` with the perturbation by the numbering `σ` of the encoding**: for the lengths `ℓ`,
`Klein.KVal` on the map with the sources copied (`Klein.srcMap`), its boundary `Klein.srcG`, the
piece `Klein.srcPiece` of the image of `fd.P'`, the perturbed lengths of `splitF_exec_enc`, the
targets the vertices `fd.Q.tail (fd.g i)`, `i < fd.k`, with `n` nodes, `n` twice the size of the
map with the sources copied. -/
def FEncValBy {X : Finset D} {B : Finset V} (fd : FaceData N X B) (ℓ : D → ℤ) (n Bw : ℕ)
    (σ : Klein.SrcD fd.DQ fd.k ≃ Fin (Fintype.card (Klein.SrcD fd.DQ fd.k))) (Pk : Input) :
    Prop :=
  n = 2 * (Fintype.card (Klein.SrcV fd.VQ fd.k) + Fintype.card (Klein.SrcF fd.FQ fd.k) +
      Fintype.card (Klein.SrcD fd.DQ fd.k)) ∧
    Klein.KVal (Klein.srcMap fd.inst.cycle) fd.k (Klein.srcG fd.inst.cycle)
      (Klein.srcPiece fd.k (fd.P'.image fd.e))
      (MSSP.pertBy σ (Klein.srcLen (faceLen fd.P' fd.e ℓ)
        (Klein.srcW (fd.P'.image fd.e) (faceLen fd.P' fd.e ℓ)))) σ n Bw fd.k
      (fun i => .inl (fd.Q.tail (fd.g i))) Pk

/-- **`fd_exec_val` with the perturbation `MSSP.pertBy σ`** (`FEncValBy`): for a
one-face instance `fd` of a part `X` (any, with `fd.q ≤ 18 m` and `fd.k² ≤ 1200 m`). -/
theorem fd_exec_valBy {P P₀ P₁ X : Finset D} (fd : FaceData N X (bdry N P₀ P₁))
    (hq : fd.q ≤ 18 * P.card) (hk : fd.k ^ 2 ≤ 1200 * P.card) {ℓ : D → ℤ}
    (hnn : ∀ d ∈ X, 0 ≤ ℓ d) {n Bw : ℕ}
    {σ : Klein.SrcD fd.DQ fd.k ≃ Fin (Fintype.card (Klein.SrcD fd.DQ fd.k))} {Pk : Input}
    (hv : FEncValBy fd ℓ n Bw σ Pk) :
      ∀ (P'' : Input) (W' β : ℕ) (d : Config), WordsBounded W' d →
        (∀ r < 201, d.nreg r ≤ Bw + 16 * (n + 1)) →
        (∀ a ≤ Bw + 16 * (n + 1), d.nmem a ≤ Bw + 16 * (n + 1)) →
        Klein.KleinEnc (Klein.srcMap fd.inst.cycle) fd.k (Klein.srcG fd.inst.cycle)
          (Klein.srcPiece fd.k (fd.P'.image fd.e))
          (MSSP.pertBy σ (Klein.srcLen (faceLen fd.P' fd.e ℓ)
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
  have hc : 2372500000 * (fd.q * lg fd.q + fd.k ^ 2 * lg fd.q) ≤
      32886 * 2372500000 * P.card * lg P.card :=
    oneFace_cost_le (f := fun q k => 2372500000 * (q * lg q + k ^ 2 * lg q))
      (fun _ _ => le_rfl) hq hk
  intro P'' W' β d hd hrb hmb hE
  obtain ⟨d', steps, ex, hs, hR, ho, h1, h2, h3, h4⟩ :=
    faceInst_exec_valBy fd.inst hnn hv.1 hv.2 P'' W' β d hd hrb hmb hE
  exact ⟨d', steps, ex, hs.trans (Nat.mul_le_mul_left 3 hc), hR, ho, h1, h2, h3, h4⟩


/-- **`FEncValBy` can be met, by the explicit words**: for every one-face instance `fd`, lengths
`ℓ` and numbering `σ` of the darts of the map with the sources copied, the words
`Klein.kInputT` of that map (`Klein.kval_kInputT`), for a layout of its nodes and initial trees
with orders (`Klein.exists_layout`, `Klein.klein_init_exists`), with the word bound `Klein.kB`,
meet `FEncValBy fd ℓ`. -/
theorem fencValBy_exists {X : Finset D} {B : Finset V} (fd : FaceData N X B) (ℓ : D → ℤ)
    (σ : Klein.SrcD fd.DQ fd.k ≃ Fin (Fintype.card (Klein.SrcD fd.DQ fd.k))) :
    ∃ (n Bw : ℕ) (Pk : Input), FEncValBy fd ℓ n Bw σ Pk := by
  classical
  have hnnQ : ∀ y ∈ fd.P'.image fd.e, 0 ≤ faceLen fd.P' fd.e ℓ y := fun y _ =>
    faceLen_nonneg _ _ _ y
  have H := (Klein.srcMap_hypNN fd.inst.cycle fd.inst.plane fd.inst.rot hnnQ
    (Klein.srcW_pos hnnQ).le).hypBy σ
  have hR := Klein.srcMap_sameReach fd.inst.cycle (S := fd.P'.image fd.e)
    (MSSP.pertBy σ (Klein.srcLen (faceLen fd.P' fd.e ℓ)
      (Klein.srcW (fd.P'.image fd.e) (faceLen fd.P' fd.e ℓ))))
  have hX : ∀ i < fd.k, ¬ MSSP.IsRoot (Klein.srcMap fd.inst.cycle) fd.k
      (Klein.srcG fd.inst.cycle) (.inl (fd.Q.tail (fd.g i))) := by
    rintro i - ⟨j, hj, hji⟩
    rw [Klein.srcTail_srcG fd.inst.cycle hj] at hji
    cases hji
  obtain ⟨ιv, ιg, ιf, ιe, hL⟩ := Klein.exists_layout (Klein.srcMap fd.inst.cycle)
  obtain ⟨T, C, vs, ts, fs, cs, hOT, hOC, hoff, hCr, hT⟩ := Klein.klein_init_exists H hR
  exact ⟨_, _, _, rfl, Klein.kval_kInputT H hX σ hL hOT hOC hoff hCr hT⟩

section PartBy

open WordRAM.Machine.Stmt WordRAM.Programs Monge

/-- **`KPartRun` with the perturbation `MSSP.pertBy σ`** (the run of one part for the instance
`fd` and its encoding): from every configuration holding the inputs in the layout `KLay`,
`kPart` runs to the
order `β'` of the boundary and the matrices of `bfStartP` for `childDDG N mssp X ℓ δ B`. -/
def KPartRunBy (N : CombMap D V F) (P P₀ P₁ X : Finset D) (ℓ : D → ℤ) (δ : V → ℤ)
    (mssp : Finset D → (D → ℤ) → Finset V → V → V → Option ℤ)
    (fd : FaceData N X (bdry N P₀ P₁)) (n Bw : ℕ)
    (σ : Klein.SrcD fd.DQ fd.k ≃ Fin (Fintype.card (Klein.SrcD fd.DQ fd.k))) (Pk : Input) :
    Prop :=
  ∀ {m w b : ℕ} {e : ℕ → D} {ν : V → ℕ} {ι : ℕ → V}, NodeEnc N P₀ P₁ m w e ν ι →
  ∀ {src : ℕ → V}, IsEnum b src (bdry N P₀ P₁) →
  ∀ (L Lb Pb δb Ys S β Rk W' : ℕ) (I : Input) (c : Config),
    KLay b w fd.k (Fintype.card (Klein.SrcD fd.DQ fd.k)) n (Bw + 16 * (n + 1)) L Lb Pb δb
      Ys S β Rk W' →
    ((Klein.srcW (fd.P'.image fd.e) (faceLen fd.P' fd.e (redLen N ℓ δ)) : ℤ) : ℝ) ≤
      2 ^ L →
    WordsBounded W' c →
    c.nreg 802 = b → c.nreg 960 = Lb → c.nreg 961 = Ys → c.nreg 962 = Ys + S →
    c.nreg 963 = Ys + 2 * S → c.nreg 964 = Ys + 3 * S → c.nreg 965 = Ys + 4 * S →
    c.nreg 966 = δb →
    (∀ i < b, c.nmem (Lb + i) = ν (src i)) →
    (∀ x ∈ bdry N P₀ P₁, c.nmem (Pb + ν x) < fd.k ∧
      fd.Q.tail (fd.g (c.nmem (Pb + ν x))) = fd.j x) →
    (∀ v < w, c.rmem (δb + v) = δ (ι v)) →
    KSlot (Klein.srcMap fd.inst.cycle) fd.k (Klein.srcG fd.inst.cycle)
      (Klein.srcPiece fd.k (fd.P'.image fd.e))
      (MSSP.pertBy σ (Klein.srcLen (faceLen fd.P' fd.e (redLen N ℓ δ))
        (Klein.srcW (fd.P'.image fd.e) (faceLen fd.P' fd.e (redLen N ℓ δ))))) σ Bw n β Rk
      W' Pk c →
    (∀ a ≤ Bw + 16 * (n + 1), c.nmem a ≤ Bw + 16 * (n + 1)) →
    ∃ c' t, ∃ β' : ℕ → V,
      Exec I W' (kPart fd.k (Fintype.card (Klein.SrcD fd.DQ fd.k)) n Bw Pk.data.length β Rk
        Pb L (Klein.srcW (fd.P'.image fd.e) (faceLen fd.P' fd.e (redLen N ℓ δ)))) c c' t ∧
      t ≤ 3 * (32886 * 2372500000 * P.card * lg P.card) +
        rdCost b L (Fintype.card (Klein.SrcD fd.DQ fd.k)) + 19 * fd.k + 10 * b +
        33 * Fintype.card (Klein.SrcD fd.DQ fd.k) + 300 ∧
      IsEnum b β' (bdry N P₀ P₁) ∧ (∀ x < b, c'.nmem (Ys + S + x) = ν (β' x)) ∧
      Monge.CrossingO b (fun i i' => (childDDG N mssp X ℓ δ (bdry N P₀ P₁)).len (β' i)
        (β' i')) ∧
      (∀ s < b, ∀ t < b,
        c'.nmem (Ys + 3 * S + (s * b + t)) =
            finB (arcOf (childDDG N mssp X ℓ δ (bdry N P₀ P₁)) β') s t ∧
          c'.rmem (Ys + 3 * S + (s * b + t)) =
            (matOf (childDDG N mssp X ℓ δ (bdry N P₀ P₁)) β' s t : ℝ)) ∧
      (∀ r, (752 ≤ r ∧ r < 900) ∨ 919 ≤ r → c'.nreg r = c.nreg r) ∧
      (∀ a, Bw + 16 * (n + 1) < a → (a < Ys ∨ Ys + 5 * S ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ a, Bw + 16 * (n + 1) < a → 3 * Fintype.card (Klein.SrcD fd.DQ fd.k) + 3 ≤ a →
        (a < Ys ∨ Ys + 5 * S ≤ a) → c'.rmem a = c.rmem a) ∧
      (∀ a ≤ Bw + 16 * (n + 1), c'.nmem a ≤ Bw + 16 * (n + 1)) ∧
      c'.output = c.output

end PartBy

section PairBy

open WordRAM.Machine.Stmt WordRAM.Programs Monge

set_option linter.unusedTactic false
set_option linter.unreachableTactic false

set_option maxHeartbeats 4000000 in
/-- **`kpair_exec` with the perturbation `MSSP.pertBy`**: two runs of `kPart` (`KPartRunBy`), in
the zones `zf ≠ zs` of the scratch area, the first with the smaller work
space of Klein's program (`Kwf ≤ Kws`): the orders and the matrices of both parts, in their
zones. -/
theorem kpair_execBy {P P₀ P₁ : Finset D} {ℓ : D → ℤ}
    {mssp : Finset D → (D → ℤ) → Finset V → V → V → Option ℤ}
    {Xf Xs : Finset D} {δf δs : V → ℤ}
    {fdf : FaceData N Xf (bdry N P₀ P₁)} {nf Bwf : ℕ}
    {σf : Klein.SrcD fdf.DQ fdf.k ≃ Fin (Fintype.card (Klein.SrcD fdf.DQ fdf.k))} {Pkf : Input}
    (hf : KPartRunBy N P P₀ P₁ Xf ℓ δf mssp fdf nf Bwf σf Pkf)
    {fds : FaceData N Xs (bdry N P₀ P₁)} {ns Bws : ℕ}
    {σs : Klein.SrcD fds.DQ fds.k ≃ Fin (Fintype.card (Klein.SrcD fds.DQ fds.k))} {Pks : Input}
    (hs : KPartRunBy N P P₀ P₁ Xs ℓ δs mssp fds ns Bws σs Pks)
    {m w b : ℕ} {e : ℕ → D} {ν : V → ℕ} {ι : ℕ → V} (hN : NodeEnc N P₀ P₁ m w e ν ι)
    {src : ℕ → V} (hsrc : IsEnum b src (bdry N P₀ P₁))
    {zf zs δrf δrs : ℕ} (hzf : zf ≤ 1) (hzs : zs ≤ 1) (hz : zf ≠ zs)
    (hδrf : 752 ≤ δrf ∧ δrf < 900) (hδrs : 752 ≤ δrs ∧ δrs < 900)
    (Lf Pbf βf Rkf δbf Ls Pbs βs Rks δbs Y S W' : ℕ) (I : Input) (c : Config)
    (hKf : KLay b w fdf.k (Fintype.card (Klein.SrcD fdf.DQ fdf.k)) nf (Bwf + 16 * (nf + 1)) Lf
      (Y + 2 * S) Pbf δbf (Y + (3 + 5 * zf) * S) S βf Rkf W')
    (hKs : KLay b w fds.k (Fintype.card (Klein.SrcD fds.DQ fds.k)) ns (Bws + 16 * (ns + 1)) Ls
      (Y + 2 * S) Pbs δbs (Y + (3 + 5 * zs) * S) S βs Rks W')
    (hWLf : ((Klein.srcW (fdf.P'.image fdf.e) (faceLen fdf.P' fdf.e (redLen N ℓ δf)) : ℤ) : ℝ) ≤
      2 ^ Lf)
    (hWLs : ((Klein.srcW (fds.P'.image fds.e) (faceLen fds.P' fds.e (redLen N ℓ δs)) : ℤ) : ℝ) ≤
      2 ^ Ls)
    (hKK : Bwf + 16 * (nf + 1) ≤ Bws + 16 * (ns + 1)) (hKY : Bws + 16 * (ns + 1) < Y)
    (hnY : 3 * Fintype.card (Klein.SrcD fdf.DQ fdf.k) + 3 ≤ Y ∧
      3 * Fintype.card (Klein.SrcD fds.DQ fds.k) + 3 ≤ Y)
    (hIn : Y + 13 * S ≤ Pbs ∧ Y + 13 * S ≤ βs ∧ Y + 13 * S ≤ Rks)
    (hδbs : δbs + w ≤ Y ∧ 3 * Fintype.card (Klein.SrcD fdf.DQ fdf.k) + 3 ≤ δbs)
    (hc : WordsBounded W' c) (h802 : c.nreg 802 = b) (hx : XCtx Y S c)
    (hrf : c.nreg δrf = δbf) (hrs : c.nreg δrs = δbs)
    (hsl : ∀ i < b, c.nmem (Y + 2 * S + i) = ν (src i))
    (hposf : ∀ x ∈ bdry N P₀ P₁, c.nmem (Pbf + ν x) < fdf.k ∧
      fdf.Q.tail (fdf.g (c.nmem (Pbf + ν x))) = fdf.j x)
    (hposs : ∀ x ∈ bdry N P₀ P₁, c.nmem (Pbs + ν x) < fds.k ∧
      fds.Q.tail (fds.g (c.nmem (Pbs + ν x))) = fds.j x)
    (hδf : ∀ v < w, c.rmem (δbf + v) = δf (ι v)) (hδs : ∀ v < w, c.rmem (δbs + v) = δs (ι v))
    (hEf : KSlot (Klein.srcMap fdf.inst.cycle) fdf.k (Klein.srcG fdf.inst.cycle)
      (Klein.srcPiece fdf.k (fdf.P'.image fdf.e))
      (MSSP.pertBy σf (Klein.srcLen (faceLen fdf.P' fdf.e (redLen N ℓ δf))
        (Klein.srcW (fdf.P'.image fdf.e) (faceLen fdf.P' fdf.e (redLen N ℓ δf))))) σf Bwf nf βf
      Rkf W' Pkf c)
    (hEs : KSlot (Klein.srcMap fds.inst.cycle) fds.k (Klein.srcG fds.inst.cycle)
      (Klein.srcPiece fds.k (fds.P'.image fds.e))
      (MSSP.pertBy σs (Klein.srcLen (faceLen fds.P' fds.e (redLen N ℓ δs))
        (Klein.srcW (fds.P'.image fds.e) (faceLen fds.P' fds.e (redLen N ℓ δs))))) σs Bws ns βs
      Rks W' Pks c)
    (hlow : ∀ a ≤ Bws + 16 * (ns + 1), c.nmem a ≤ Bwf + 16 * (nf + 1)) :
    ∃ c' t, ∃ βf' βs' : ℕ → V,
      Exec I W' (kPair zf δrf fdf.k (Fintype.card (Klein.SrcD fdf.DQ fdf.k)) nf Bwf
        Pkf.data.length βf Rkf Pbf Lf
        (Klein.srcW (fdf.P'.image fdf.e) (faceLen fdf.P' fdf.e (redLen N ℓ δf)))
        zs δrs fds.k (Fintype.card (Klein.SrcD fds.DQ fds.k)) ns Bws Pks.data.length βs Rks Pbs
        Ls (Klein.srcW (fds.P'.image fds.e) (faceLen fds.P' fds.e (redLen N ℓ δs)))) c c' t ∧
      t ≤ (3 * (32886 * 2372500000 * P.card * lg P.card) +
            rdCost b Lf (Fintype.card (Klein.SrcD fdf.DQ fdf.k)) + 19 * fdf.k + 10 * b +
            33 * Fintype.card (Klein.SrcD fdf.DQ fdf.k) + 300) +
          (3 * (32886 * 2372500000 * P.card * lg P.card) +
            rdCost b Ls (Fintype.card (Klein.SrcD fds.DQ fds.k)) + 19 * fds.k + 10 * b +
            33 * Fintype.card (Klein.SrcD fds.DQ fds.k) + 300) + 14 ∧
      IsEnum b βf' (bdry N P₀ P₁) ∧
      (∀ x < b, c'.nmem (Y + (3 + 5 * zf) * S + S + x) = ν (βf' x)) ∧
      Monge.CrossingO b (fun i i' => (childDDG N mssp Xf ℓ δf (bdry N P₀ P₁)).len (βf' i)
        (βf' i')) ∧
      (∀ s < b, ∀ t < b,
        c'.nmem (Y + (3 + 5 * zf) * S + 3 * S + (s * b + t)) =
            finB (arcOf (childDDG N mssp Xf ℓ δf (bdry N P₀ P₁)) βf') s t ∧
          c'.rmem (Y + (3 + 5 * zf) * S + 3 * S + (s * b + t)) =
            (matOf (childDDG N mssp Xf ℓ δf (bdry N P₀ P₁)) βf' s t : ℝ)) ∧
      IsEnum b βs' (bdry N P₀ P₁) ∧
      (∀ x < b, c'.nmem (Y + (3 + 5 * zs) * S + S + x) = ν (βs' x)) ∧
      Monge.CrossingO b (fun i i' => (childDDG N mssp Xs ℓ δs (bdry N P₀ P₁)).len (βs' i)
        (βs' i')) ∧
      (∀ s < b, ∀ t < b,
        c'.nmem (Y + (3 + 5 * zs) * S + 3 * S + (s * b + t)) =
            finB (arcOf (childDDG N mssp Xs ℓ δs (bdry N P₀ P₁)) βs') s t ∧
          c'.rmem (Y + (3 + 5 * zs) * S + 3 * S + (s * b + t)) =
            (matOf (childDDG N mssp Xs ℓ δs (bdry N P₀ P₁)) βs' s t : ℝ)) ∧
      (∀ r, (800 ≤ r ∧ r < 900) ∨ (919 ≤ r ∧ r < 960) ∨ 967 ≤ r → c'.nreg r = c.nreg r) ∧
      (∀ a, Bws + 16 * (ns + 1) < a → (a < Y + 3 * S ∨ Y + 13 * S ≤ a) →
        c'.nmem a = c.nmem a) ∧
      (∀ a, Bws + 16 * (ns + 1) < a → 3 * Fintype.card (Klein.SrcD fdf.DQ fdf.k) + 3 ≤ a →
        3 * Fintype.card (Klein.SrcD fds.DQ fds.k) + 3 ≤ a →
        (a < Y + 3 * S ∨ Y + 13 * S ≤ a) → c'.rmem a = c.rmem a) ∧
      c'.output = c.output := by
  have hx' := hx.reg
  obtain ⟨hδrf1, hδrf2⟩ := hδrf
  obtain ⟨hδrs1, hδrs2⟩ := hδrs
  obtain ⟨hnY1, hnY2⟩ := hnY
  obtain ⟨hIn1, hIn2, hIn3⟩ := hIn
  obtain ⟨hδbs1, hδbs2⟩ := hδbs
  have hKf' := hKf
  have hKs' := hKs
  obtain ⟨sk, sb, sbb, snD, kY, rbY, outY, yW, lK, lY, lW, pK, pY, pW, dK, dnD, dY, dW, bY, rK,
    rnD, rY, rW, bbW, lLW, wW⟩ := hKf'
  obtain ⟨sk', sb', sbb', snD', kY', rbY', outY', yW', lK', lY', lW', pK', pY', pW', dK', dnD',
    dY', dW', bY', rK', rnD', rY', rW', bbW', lLW', wW'⟩ := hKs'
  -- 1., 2. the first part
  obtain ⟨c₁, k₁, e₁, hk₁, a960, a961, a962, a963, a964, a965, a966, an₁, anm₁, arm₁, ao₁⟩ :=
    partSet_exec (I := I) (δr := δrf) hzf (by omega) c hc
  have z1 : ∀ i ≤ 4, c.nreg (933 + 5 * zf + i) = Y + (3 + 5 * zf) * S + i * S := fun i hi => by
    rw [show 933 + 5 * zf + i = 930 + (3 + 5 * zf + i) by omega, hx' _ (by omega)]; ring
  obtain ⟨c₂, k₂, βf', e₂, hk₂, hen₂, hO₂, hcr₂, hF₂, hn₂, hm₂, hr₂, hl₂, ho₂⟩ :=
    hf hN hsrc Lf (Y + 2 * S) Pbf δbf (Y + (3 + 5 * zf) * S) S βf Rkf W' I c₁ hKf hWLf
      e₁.wb_right (by rw [an₁ 802 (by omega), h802])
      (by rw [a960, hx' 2 (by omega)])
      (by rw [a961, show 933 + 5 * zf = 933 + 5 * zf + 0 by rfl, z1 0 (by omega)]; ring)
      (by rw [a962, show 934 + 5 * zf = 933 + 5 * zf + 1 by omega, z1 1 (by omega)]; ring)
      (by rw [a963, show 935 + 5 * zf = 933 + 5 * zf + 2 by omega, z1 2 (by omega)])
      (by rw [a964, show 936 + 5 * zf = 933 + 5 * zf + 3 by omega, z1 3 (by omega)])
      (by rw [a965, show 937 + 5 * zf = 933 + 5 * zf + 4 by omega, z1 4 (by omega)])
      (by rw [a966, hrf])
      (fun i hi => by rw [anm₁]; exact hsl i hi)
      (fun x hx => by rw [anm₁]; exact hposf x hx)
      (fun v hv => by rw [arm₁]; exact hδf v hv)
      (hEf.of (fun i _ => by rw [arm₁]) (fun i _ => by rw [anm₁]))
      (fun a ha => by rw [anm₁]; exact (hlow a (by omega)).trans le_rfl |>.trans (by omega))
  have z2 : ∀ i ≤ 4, c.nreg (933 + 5 * zs + i) = Y + (3 + 5 * zs) * S + i * S := fun i hi => by
    rw [show 933 + 5 * zs + i = 930 + (3 + 5 * zs + i) by omega, hx' _ (by pomega)]; ring
  have hx2 := hx' 2 (by pomega)
  -- 3., 4. the second part
  obtain ⟨c₃, k₃, e₃, hk₃, b960, b961, b962, b963, b964, b965, b966, bn₃, bnm₃, brm₃, bo₃⟩ :=
    partSet_exec (I := I) (δr := δrs) hzs (by pomega) c₂ e₂.wb_right
  obtain ⟨Af, As, hAf, hAs, hA⟩ : ∃ Af As, Y + (3 + 5 * zf) * S = Y + 3 * S + Af ∧
      Y + (3 + 5 * zs) * S = Y + 3 * S + As ∧ ((Af = 0 ∧ As = 5 * S) ∨ (Af = 5 * S ∧ As = 0)) := by
    rcases (by omega : (zf = 0 ∧ zs = 1) ∨ (zf = 1 ∧ zs = 0)) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨0, 5 * S, by ring, by ring, Or.inl ⟨rfl, rfl⟩⟩
    · exact ⟨5 * S, 0, by ring, by ring, Or.inr ⟨rfl, rfl⟩⟩
  simp only [hAf, hAs] at *
  have hR₂ : ∀ r, (800 ≤ r ∧ r < 900) ∨ (919 ≤ r ∧ r < 960) ∨ 967 ≤ r ∨ r = δrs →
      c₂.nreg r = c.nreg r := fun r hr => by rw [hn₂ r (by pomega), an₁ r (by pomega)]
  have hm₂' : ∀ a, Bwf + 16 * (nf + 1) < a → (a < Y + 3 * S + Af ∨ Y + 3 * S + Af + 5 * S ≤ a) →
      c₂.nmem a = c.nmem a := fun a h1 h2 => by rw [hm₂ a h1 h2, anm₁]
  have hr₂' : ∀ a, Bwf + 16 * (nf + 1) < a → 3 * Fintype.card (Klein.SrcD fdf.DQ fdf.k) + 3 ≤ a →
      (a < Y + 3 * S + Af ∨ Y + 3 * S + Af + 5 * S ≤ a) → c₂.rmem a = c.rmem a :=
    fun a h1 h2 h3 => by rw [hr₂ a h1 h2 h3, arm₁]
  obtain ⟨c₄, k₄, βs', e₄, hk₄, hen₄, hO₄, hcr₄, hF₄, hn₄, hm₄, hr₄, hl₄, ho₄⟩ :=
    hs hN hsrc Ls (Y + 2 * S) Pbs δbs (Y + 3 * S + As) S βs Rks W' I c₃ hKs hWLs
      e₃.wb_right (by rw [bn₃ 802 (by pomega), hR₂ 802 (by pomega), h802])
      (by rw [b960, hR₂ 932 (by pomega), hx2])
      (by rw [b961, show 933 + 5 * zs = 933 + 5 * zs + 0 by rfl, hR₂ _ (by pomega),
        z2 0 (by pomega)]; ring)
      (by rw [b962, show 934 + 5 * zs = 933 + 5 * zs + 1 by omega, hR₂ _ (by pomega),
        z2 1 (by pomega)]; ring)
      (by rw [b963, show 935 + 5 * zs = 933 + 5 * zs + 2 by omega, hR₂ _ (by pomega),
        z2 2 (by pomega)])
      (by rw [b964, show 936 + 5 * zs = 933 + 5 * zs + 3 by omega, hR₂ _ (by pomega),
        z2 3 (by pomega)])
      (by rw [b965, show 937 + 5 * zs = 933 + 5 * zs + 4 by omega, hR₂ _ (by pomega),
        z2 4 (by pomega)])
      (by rw [b966, hR₂ δrs (by pomega), hrs])
      (fun i hi => by rw [bnm₃, hm₂' _ (by pomega) (by pomega)]; exact hsl i hi)
      (fun x hx => by
        have := hN.lt _ (bdry_sub_verts hx)
        rw [bnm₃, hm₂' _ (by pomega) (by pomega)]; exact hposs x hx)
      (fun v hv => by rw [brm₃, hr₂' _ (by pomega) (by pomega) (by pomega)]; exact hδs v hv)
      (hEs.of (fun i _ => by rw [brm₃, hr₂' _ (by pomega) (by pomega) (by pomega)])
        (fun i _ => by rw [bnm₃, hm₂' _ (by pomega) (by pomega)]))
      (fun a ha => by
        rw [bnm₃]
        by_cases h1 : a ≤ Bwf + 16 * (nf + 1)
        · exact (hl₂ a h1).trans hKK
        · rw [hm₂' a (by pomega) (by pomega)]; exact (hlow a ha).trans hKK)
  clear hlow hposs hposf hsl hδf hδs hEf hEs hf hs
  refine ⟨c₄, k₁ + (k₂ + (k₃ + k₄)), βf', βs', Exec.seq e₁ (Exec.seq e₂ (Exec.seq e₃ e₄)), ?_,
    hen₂, fun x hx => ?_, hcr₂, fun s' hs' t ht => ?_, hen₄, hO₄, hcr₄, hF₄, fun r hr => ?_,
    fun a h1 h2 => ?_, fun a h1 h2 h2' h3 => ?_, by rw [ho₄, bo₃, ho₂, ao₁]⟩
  · pomega
  · rw [hm₄ _ (by pomega) (by pomega), bnm₃]; exact hO₂ x hx
  · have := rmLt hs' ht
    rw [hm₄ _ (by pomega) (by pomega), bnm₃, hr₄ _ (by pomega) (by pomega) (by pomega), brm₃]
    exact hF₂ s' hs' t ht
  · rw [hn₄ r (by pomega), bn₃ r (by pomega), hR₂ r (by pomega)]
  · rw [hm₄ a (by pomega) (by pomega), bnm₃, hm₂' a (by pomega) (by pomega)]
  · rw [hr₄ a (by pomega) (by pomega) (by pomega), brm₃, hr₂' a (by pomega) (by pomega) (by pomega)]

end PairBy

open WordRAM.Machine.Stmt WordRAM.Programs Monge


set_option maxHeartbeats 4000000 in
/-- **`kpart_exec_val` with the perturbation `MSSP.pertBy σ`** (`FEncValBy`, `KPartRunBy`): for
any one-face instance `fd` of the part `X` (with `fd.q ≤ 18 m`, `fd.k² ≤ 1200 m`) and any
encoding meeting
`FEncValBy fd (redLen N ℓ δ)`, the run of the part `KPartRunBy` holds. -/
theorem kpart_exec_valBy {P P₀ P₁ X : Finset D} (fd : FaceData N X (bdry N P₀ P₁))
    (hq : fd.q ≤ 18 * P.card) (hk : fd.k ^ 2 ≤ 1200 * P.card) {ℓ : D → ℤ} {δ : V → ℤ}
    (hnn : ∀ d ∈ X, 0 ≤ redLen N ℓ δ d)
    {mssp : Finset D → (D → ℤ) → Finset V → V → V → Option ℤ} (hmssp : PieceMSSPSpec N mssp)
    {n Bw : ℕ} {σ : Klein.SrcD fd.DQ fd.k ≃ Fin (Fintype.card (Klein.SrcD fd.DQ fd.k))}
    {Pk : Input} (hv : FEncValBy fd (redLen N ℓ δ) n Bw σ Pk) :
    KPartRunBy N P P₀ P₁ X ℓ δ mssp fd n Bw σ Pk := by
  classical
  have hrun := fd_exec_valBy fd hq hk hnn hv
  unfold KPartRunBy
  intro m w b e ν ι hN src hsrc L Lb Pb δb Ys S β Rk W' I c hL hWL hc r802 r960 r961 r962 r963
    r964 r965 r966 hsl hpos hδ hK hlow
  set nD := Fintype.card (Klein.SrcD fd.DQ fd.k) with hnD
  set Kw := Bw + 16 * (n + 1) with hKw
  set Wr := Klein.srcW (fd.P'.image fd.e) (faceLen fd.P' fd.e (redLen N ℓ δ)) with hWr
  obtain ⟨sk, sb, sbb, snD, kY, rbY, outY, yW, lK, lY, lW, pK, pY, pW, dK, dnD, dY, dW, bY, rK, rnD,
    rY, rW, bbW, lLW, wW⟩ := hL
  have hνlt : ∀ i < b, ν (src i) < w := fun i hi => hN.lt _ (bdry_sub_verts (hsrc.mem i hi))
  -- 1. the registers of `cornerProg`
  obtain ⟨c₁, t₁, e₁, ht₁, g10, g740, g741, g742, g743, g744, g745, g746, gn₁, -, gnm₁, grm₁,
    go₁⟩ := kpC_exec (I := I) (k := fd.k) (Pb := Pb) (by pomega) (by pomega) c hc (by pomega)
  -- 2. the corners
  have hCL : CornerLay fd.k b w Lb Pb Ys (Ys + S) (Ys + 2 * S) W' (fun i => ν (src i)) :=
    ⟨hνlt, by pomega, by pomega, by pomega, by pomega, by pomega, by pomega, by pomega,
      by pomega, by pomega, by pomega, by pomega, by pomega, by pomega⟩
  have hCI : CornerIn fd.k b Lb Pb Ys (Ys + S) (Ys + 2 * S) (fun i => ν (src i)) c₁ :=
    ⟨g10, g740, by rw [g741, r802], by rw [g742, r960], g743, by rw [g744, r961],
      by rw [g745, r962], by rw [g746, r963], fun i hi => by rw [gnm₁]; exact hsl i hi⟩
  obtain ⟨c₂, t₂, β', e₂, ht₂, -, hen, hO₂, hS₂, hcr, hfr₂, hcf₂⟩ :=
    cornerProg_crossingO (P := I) fd.inst hsrc hCL c₁ e₁.wb_right hCI
      (fun i hi => by rw [gnm₁]; exact hpos _ (hsrc.mem i hi))
  have hR₂ : ∀ r, (752 ≤ r ∧ r < 900) ∨ 919 ≤ r → c₂.nreg r = c.nreg r := fun r hr => by
    rw [hcf₂.nreg r (by pomega), gn₁ r (by pomega) (by pomega)]
  -- 3., 4. the real constants copied down
  obtain ⟨c₃, t₃, e₃, ht₃, k910, k911, k912, k913, k914, gn₃, -, gnm₃, grm₃, go₃⟩ :=
    kpK_exec (I := I) (nD := nD) (Rk := Rk) (by pomega) (by pomega) c₂ e₂.wb_right
  have hCp : CpyLay (3 * nD + 3) (Ys + 4 * S) Rk 0 Rk W' :=
    ⟨by pomega, by pomega, by pomega, by pomega, by pomega, by pomega, by pomega⟩
  obtain ⟨c₄, t₄, e₄, ht₄, hcp₄, hn₄, hr₄, hreg₄, -, ho₄⟩ := cpyProg_exec (P := I) hCp c₃
    e₃.wb_right k910 (by rw [k911, hR₂ 965 (by pomega), r965]) k912 k913 k914
  have hR₄ : ∀ r, (752 ≤ r ∧ r < 900) ∨ 919 ≤ r → c₄.nreg r = c.nreg r := fun r hr => by
    rw [hreg₄ r (by pomega), gn₃ r (by pomega), hR₂ r hr]
  -- 5. the registers of Klein's program cleared
  obtain ⟨c₅, t₅, e₅, ht₅, hz₅, -, hnm₅, hrm₅, ho₅⟩ :=
    zeroRegs_exec (P := I) (List.range 201) c₄ e₄.wb_right
  have hR₅ : ∀ r, (752 ≤ r ∧ r < 900) ∨ 919 ≤ r → c₅.nreg r = c.nreg r := fun r hr => by
    rw [hz₅ r, ite_eq_right_of_eq_false _ _ (eq_false (by simp; pomega)), hR₄ r hr]
  -- the natural memory outside the regions, up to here
  have hm₅ : ∀ a, (a < Ys ∨ Ys + 5 * S ≤ a) → c₅.nmem a = c.nmem a := fun a ha => by
    rw [hnm₅, hn₄ a (by pomega), gnm₃, hfr₂ a (by pomega) (by pomega) (by pomega), gnm₁]
  -- 6. Klein's program
  have hE := hK.enc (d := c₅)
    (fun i hi => by
      have := (hcp₄ i hi).2; rw [zero_add] at this
      rw [hrm₅, this, grm₃, hcf₂.rmem, grm₁])
    (fun i hi => hm₅ _ (by pomega))
  obtain ⟨d', s₆, e₆, hs₆, hR₆, ho₆, h1₆, -, h3₆, h4₆, h5₆⟩ := hrun I W' β c₅ e₅.wb_right
    (fun r hr => by rw [hz₅ r, ite_eq_left_of_eq_true _ _ (eq_true (by simp; omega))]; exact Nat.zero_le _)
    (fun a ha => by rw [hm₅ a (by pomega)]; exact hlow a ha) hE
  have hQ₆ : ∀ r, (752 ≤ r ∧ r < 900) ∨ 919 ≤ r → d'.nreg r = c.nreg r := fun r hr => by
    rw [h1₆ r (by pomega), hR₅ r hr]
  -- 7. the registers of `rdProg`
  obtain ⟨c₇, t₇, e₇, ht₇, q300, q301, q302, q303, q304, q305, q306, q307, q308, q309, q310,
    w301, gn₇, gnm₇, grm₇, go₇⟩ := kpR_exec (I := I) (k := fd.k) (nD := nD) (n := n) (L := L)
      (Wr := Wr) (by pomega) (by pomega) (by pomega) (by pomega) d' e₆.wb_right
  -- 8. the reading
  let R : Rd := ⟨b, fd.k, w, Ys + 2 * S, Ys + S, δb, n, 3 * nD + 3, Ys + 3 * S, Ys + 3 * S, L,
    nD, fun s => c₂.nmem (Ys + 2 * S + s), fun s => ν (β' s), (Wr : ℝ)⟩
  have hm₇ : ∀ a, Kw < a → a < Ys + 4 * S → c₇.nmem a = c₂.nmem a :=
    fun a ha ha' => by rw [gnm₇, h3₆ a ha, hnm₅, hn₄ a (by pomega), gnm₃]
  have hRL : RdLay R W' := by
    refine ⟨fun s hs => (hS₂ s hs).1, fun s hs => hN.lt _ (bdry_sub_verts (hen.mem s hs)),
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals dsimp only [R]; pomega
  have hR₇ : ∀ r, (752 ≤ r ∧ r < 900) ∨ 919 ≤ r → c₇.nreg r = c.nreg r := fun r hr => by
    rw [gn₇ r (by pomega), hQ₆ r hr]
  have hRI : RdIn R c₇ := by
    refine ⟨?_, ?_, ?_, ?_, q304, q305, q306, ?_, ?_, q309, q310, w301, fun s hs => ?_,
      fun s hs => ?_⟩
    · rw [q300, hQ₆ 802 (by pomega), r802]
    · rw [q301, hQ₆ 963 (by pomega), r963]
    · rw [q302, hQ₆ 962 (by pomega), r962]
    · rw [q303, hQ₆ 966 (by pomega), r966]
    · rw [q307, hQ₆ 964 (by pomega), r964]
    · rw [q308, hQ₆ 964 (by pomega), r964]
    · dsimp only [R] at hs ⊢; exact hm₇ _ (by pomega) (by pomega)
    · dsimp only [R] at hs ⊢; rw [hm₇ _ (by pomega) (by pomega)]; exact hO₂ s hs
  obtain ⟨c₈, t₈, e₈, ht₈, hO₈, hn₈, hr₈, hreg₈, ho₈⟩ :=
    rdProg_exec' (I := I) hRL hWL c₇ e₇.wb_right hRI
  have hn₈' : ∀ a, (a < Ys + 3 * S ∨ Ys + 3 * S + b * b ≤ a) → c₈.nmem a = c₇.nmem a := hn₈
  have hr₈' : ∀ a, (a < Ys + 3 * S ∨ Ys + 3 * S + b * b ≤ a) → c₈.rmem a = c₇.rmem a := hr₈
  clear hn₈ hr₈
  refine ⟨c₈, t₁ + (t₂ + (t₃ + (t₄ + (t₅ + (s₆ + (t₇ + t₈)))))), β',
    Exec.seq e₁ (Exec.seq e₂ (Exec.seq e₃ (Exec.seq e₄ (Exec.seq e₅ (Exec.seq e₆
      (Exec.seq e₇ e₈)))))), ?_, hen, fun x hx => ?_, hcr hmssp hnn, fun s hs t ht => ?_,
    fun r hr => ?_, fun a ha ha'' => ?_, fun a ha ha' ha'' => ?_, fun a ha => ?_, ?_⟩
  · -- the cost
    have : t₈ ≤ rdCost b L nD := ht₈
    simp only [List.length_range] at ht₅
    pomega
  · -- the order
    rw [hn₈' _ (Or.inl (by pomega)), hm₇ _ (by pomega) (by pomega)]; exact hO₂ x hx
  · -- the matrices
    have hsB := hen.mem s hs
    have htB := hen.mem t ht
    obtain ⟨i, hi, hib, hK'⟩ := hR₆ (β' s) hsB
    obtain ⟨i', hi', hib', hK''⟩ := hK' (β' t) htB
    have hii : i = R.σ s :=
      fd.inst.cycle.inj i hi (R.σ s) (hS₂ s hs).1 (hib.trans (hS₂ s hs).2)
    have hii' : i' = R.σ t :=
      fd.inst.cycle.inj i' hi' (R.σ t) (hS₂ t ht).1 (hib'.trans (hS₂ t ht).2)
    subst hii hii'
    have hnn' : ∀ a, 0 ≤ (MSSP.pieceGraph N X (redLen N ℓ δ)).len a := fun a => hnn a.1 a.2
    have hms : mssp X (redLen N ℓ δ) (bdry N P₀ P₁) (β' s) (β' t) =
        MSSP.odist (MSSP.pieceGraph N X (redLen N ℓ δ)) (β' s) (β' t) := by
      have := odist_eq_of_isDist hnn' (hmssp X (redLen N ℓ δ) (bdry N P₀ P₁) hnn (β' s) hsB)
      exact congrFun this (β' t)
    have hk7 : Klein.kOut nD n R.k c₇ (R.σ s) (R.σ t) = Klein.kOut nD n fd.k d' (R.σ s) (R.σ t) := by
      unfold Klein.kOut; rw [gnm₇, grm₇]
    have hA : Klein.srcOut Wr R.M (Klein.kOut nD n R.k c₇ (R.σ s) (R.σ t)) =
        MSSP.odist (MSSP.pieceGraph N X (redLen N ℓ δ)) (β' s) (β' t) := by
      rw [hk7]; exact hK''
    have hd : ∀ x < b, c₇.rmem (R.δb + R.ν x) = δ (β' x) := fun x hx => by
      have hv := bdry_sub_verts (hen.mem x hx)
      show c₇.rmem (δb + ν (β' x)) = δ (β' x)
      rw [grm₇, h4₆ _ (by pomega), hrm₅, hr₄ _ (Or.inr (by pomega)), grm₃, hcf₂.rmem, grm₁,
        hδ _ (hN.lt _ hv), hN.inv _ hv]
    refine rdOut_child (R := R) (Wc := Wr) rfl rfl rfl ?_ ?_ (hd s hs) (hd t ht)
      (hO₈ s hs t ht)
    · show (mssp X (redLen N ℓ δ) (bdry N P₀ P₁) (β' s) (β' t)).map
        (· + (δ (β' t) - δ (β' s))) = _
      rw [hms, hA]
    · intro z hz
      rw [hA] at hz
      unfold MSSP.odist at hz
      split_ifs at hz with hr
      · cases hz; exact MSSP.dist_nonneg hnn' hr
  · -- the registers
    rw [hreg₈ r (by pomega)]; exact hR₇ r hr
  · -- the memory
    rw [hn₈' a (by pomega), gnm₇, h3₆ a ha, hm₅ a ha'']
  · rw [hr₈' a (by pomega), grm₇, h4₆ a ha, hrm₅, hr₄ a (Or.inr (by pomega)), grm₃,
      hcf₂.rmem, grm₁]
  · -- the work space
    rw [hn₈' a (Or.inl (by pomega)), gnm₇]; exact h5₆ a ha
  · rw [ho₈, go₇, ho₆, ho₅, ho₄, go₃, hcf₂.out, go₁]

open Monge.FR

set_option maxHeartbeats 8000000 in
/-- **`node_exec_val` with the perturbation `MSSP.pertBy`**: the whole node as one run, for every
pair of instances and encodings meeting `FEncValBy` (`node_exec` with the instances `fd₀`, `fd₁`
and their encodings as inputs: any
one-face instances of the two parts with `fd.q ≤ 18 m`, `fd.k² ≤ 1200 m`, any encodings
meeting `FEncVal` for the reduced lengths). -/
theorem node_exec_valBy (C : ℕ) {fr : FRFun (Option V)} (hfr : FRSpec fr)
    {mssp : Finset D → (D → ℤ) → Finset V → V → V → Option ℤ} (hmssp : PieceMSSPSpec N mssp)
    {P P₀ P₁ : Finset D} (hS : SplitF N P P₀ P₁) (hB : (bdry N P₀ P₁).Nonempty) (ℓ : D → ℤ)
    (δ₀ δ₁ : V → ℤ) (hδ₀ : (pg N P₀ ℓ).IsPot δ₀) (hδ₁ : (pg N P₁ ℓ).IsPot δ₁)
    (fd₀ : FaceData N P₀ (bdry N P₀ P₁)) (hq₀ : fd₀.q ≤ 18 * P.card)
    (hk₀ : fd₀.k ^ 2 ≤ 1200 * P.card) {n₀ Bw₀ : ℕ}
    {σ₀ : Klein.SrcD fd₀.DQ fd₀.k ≃ Fin (Fintype.card (Klein.SrcD fd₀.DQ fd₀.k))} {Pk₀ : Input}
    (hv₀ : FEncValBy fd₀ (redLen N ℓ δ₀) n₀ Bw₀ σ₀ Pk₀)
    (fd₁ : FaceData N P₁ (bdry N P₀ P₁)) (hq₁ : fd₁.q ≤ 18 * P.card)
    (hk₁ : fd₁.k ^ 2 ≤ 1200 * P.card) {n₁ Bw₁ : ℕ}
    {σ₁ : Klein.SrcD fd₁.DQ fd₁.k ≃ Fin (Fintype.card (Klein.SrcD fd₁.DQ fd₁.k))} {Pk₁ : Input}
    (hv₁ : FEncValBy fd₁ (redLen N ℓ δ₁) n₁ Bw₁ σ₁ Pk₁) :
      ∀ {m w b : ℕ} {e : ℕ → D} {ν : V → ℕ} {ι : ℕ → V}, NodeEnc N P₀ P₁ m w e ν ι →
      b = (bdry N P₀ P₁).card →
      ∀ (L₀ L₁ Pb₀ Pb₁ β₀ β₁ Rk₀ Rk₁ Z M₀ Y S W' : ℕ) (I : Input) (c : Config),
        M₀ = m + w + 1 → loB m w ≤ Z → bfWP b < Z →
        Bw₀ + 16 * (n₀ + 1) < Z → Bw₁ + 16 * (n₁ + 1) < Z →
        n₀ + fd₀.k * fd₀.k ≤ Z → n₁ + fd₁.k * fd₁.k ≤ Z →
        3 * Fintype.card (Klein.SrcD fd₀.DQ fd₀.k) + 3 + fd₀.k * fd₀.k ≤ Z →
        3 * Fintype.card (Klein.SrcD fd₁.DQ fd₁.k) + 3 + fd₁.k * fd₁.k ≤ Z →
        Z + 22 * M₀ ≤ Y →
        (w ≤ S ∧ b * b ≤ S ∧ fd₀.k ≤ S ∧ fd₁.k ≤ S ∧ 3 * Fintype.card (Klein.SrcD fd₀.DQ fd₀.k) + 3 ≤ S ∧
          3 * Fintype.card (Klein.SrcD fd₁.DQ fd₁.k) + 3 ≤ S) →
        (Y + 16 * S ≤ Pb₀ ∧ Y + 16 * S ≤ Pb₁ ∧ Y + 16 * S ≤ β₀ ∧ Y + 16 * S ≤ β₁ ∧
          Y + 16 * S ≤ Rk₀ ∧ Y + 16 * S ≤ Rk₁) →
        (Y + 16 * S ≤ W' ∧ Pb₀ + w ≤ W' ∧ Pb₁ + w ≤ W' ∧ Rk₀ + (3 * Fintype.card (Klein.SrcD fd₀.DQ fd₀.k) + 3) ≤ W' ∧
          Rk₁ + (3 * Fintype.card (Klein.SrcD fd₁.DQ fd₁.k) + 3) ≤ W' ∧ L₀ + 1 ≤ W' ∧ L₁ + 1 ≤ W') →
        ((Klein.srcW (fd₀.P'.image fd₀.e) (faceLen fd₀.P' fd₀.e (redLen N ℓ δ₀)) : ℤ) : ℝ) ≤ 2 ^ L₀ →
        ((Klein.srcW (fd₁.P'.image fd₁.e) (faceLen fd₁.P' fd₁.e (redLen N ℓ δ₁)) : ℤ) : ℝ) ≤ 2 ^ L₁ →
        WordsBounded W' c → NCtx m w b Z M₀ c → XCtx Y S c →
        (∀ d < m, c.nmem (Z + 0 * M₀ + d) = encT N e ν d) →
        (∀ d < m, c.nmem (Z + 1 * M₀ + d) = encH N e ν d) →
        (∀ d < m, c.nmem (Z + 2 * M₀ + d) = encS P₀ e d) →
        (∀ d < m, c.rmem (Z + 3 * M₀ + d) = ℓ (e d)) →
        (∀ v < w, c.rmem (Z + 4 * M₀ + v) = δ₀ (ι v)) →
        (∀ v < w, c.rmem (Z + 5 * M₀ + v) = δ₁ (ι v)) →
        (∀ a < Z, c.nmem a = 0) →
        (∀ x ∈ bdry N P₀ P₁, c.nmem (Pb₀ + ν x) < fd₀.k ∧
          fd₀.Q.tail (fd₀.g (c.nmem (Pb₀ + ν x))) = fd₀.j x) →
        (∀ x ∈ bdry N P₀ P₁, c.nmem (Pb₁ + ν x) < fd₁.k ∧
          fd₁.Q.tail (fd₁.g (c.nmem (Pb₁ + ν x))) = fd₁.j x) →
        KSlot (Klein.srcMap fd₀.inst.cycle) fd₀.k (Klein.srcG fd₀.inst.cycle)
          (Klein.srcPiece fd₀.k (fd₀.P'.image fd₀.e))
          (MSSP.pertBy σ₀ (Klein.srcLen (faceLen fd₀.P' fd₀.e (redLen N ℓ δ₀))
            (Klein.srcW (fd₀.P'.image fd₀.e) (faceLen fd₀.P' fd₀.e (redLen N ℓ δ₀)))))
          σ₀ Bw₀ n₀ β₀ Rk₀ W' Pk₀ c →
        KSlot (Klein.srcMap fd₁.inst.cycle) fd₁.k (Klein.srcG fd₁.inst.cycle)
          (Klein.srcPiece fd₁.k (fd₁.P'.image fd₁.e))
          (MSSP.pertBy σ₁ (Klein.srcLen (faceLen fd₁.P' fd₁.e (redLen N ℓ δ₁))
            (Klein.srcW (fd₁.P'.image fd₁.e) (faceLen fd₁.P' fd₁.e (redLen N ℓ δ₁)))))
          σ₁ Bw₁ n₁ β₁ Rk₁ W' Pk₁ c →
        ∃ c' t, ∃ o : Option (V → ℤ),
          Exec I W' (nodeProg ⟨fd₀.k, Fintype.card (Klein.SrcD fd₀.DQ fd₀.k), n₀, Bw₀, Pk₀.data.length, β₀, Rk₀, Pb₀, L₀,
          Klein.srcW (fd₀.P'.image fd₀.e) (faceLen fd₀.P' fd₀.e (redLen N ℓ δ₀))⟩
            ⟨fd₁.k, Fintype.card (Klein.SrcD fd₁.DQ fd₁.k), n₁, Bw₁, Pk₁.data.length, β₁, Rk₁, Pb₁, L₁,
          Klein.srcW (fd₁.P'.image fd₁.e) (faceLen fd₁.P' fd₁.e (redLen N ℓ δ₁))⟩) c c' t ∧
          t ≤ 8 + (61 * m + 12) +
          ((3 * (32886 * 2372500000 * P.card * lg P.card) + rdCost b L₀ (Fintype.card (Klein.SrcD fd₀.DQ fd₀.k)) + 19 * fd₀.k + 10 * b +
            33 * Fintype.card (Klein.SrcD fd₀.DQ fd₀.k) + 300) +
          (3 * (32886 * 2372500000 * P.card * lg P.card) + rdCost b L₁ (Fintype.card (Klein.SrcD fd₁.DQ fd₁.k)) + 19 * fd₁.k + 10 * b +
            33 * Fintype.card (Klein.SrcD fd₁.DQ fd₁.k) + 300) + 14) +
          (bfCostP b + 4 * bfWP b + 22 * (b * b) + 2 * (cNegMach C).dij (w + 1) (m + w) +
            232 * m + 450 * w + 92 * b + 2917) ∧
          PotOut ((childDDG N mssp P₀ ℓ δ₀ (bdry N P₀ P₁)).join (childDDG N mssp P₁ ℓ δ₁ (bdry N P₀ P₁))) o ∧
          (∀ bf : DDG V → DDG V → Option (V → ℤ), bf (childDDG N mssp P₀ ℓ δ₀ (bdry N P₀ P₁)) (childDDG N mssp P₁ ℓ δ₁ (bdry N P₀ P₁)) = o →
            (step N mssp bf fr P₀ P₁ ℓ δ₀ δ₁ = none ∧ c'.nreg 990 ≠ 0) ∨
            (∃ f, step N mssp bf fr P₀ P₁ ℓ δ₀ δ₁ = some f ∧ c'.nreg 990 = 0 ∧
              ∀ x ∈ verts N (P₀ ∪ P₁), c'.rmem (Z + 20 * M₀ + ν x) = f x)) ∧
          c'.output = c.output := by
  classical
  have hnn₀ := redLen_nonneg hδ₀
  have hnn₁ := redLen_nonneg hδ₁
  have hr₀ : KPartRunBy N P P₀ P₁ P₀ ℓ δ₀ mssp fd₀ n₀ Bw₀ σ₀ Pk₀ :=
    kpart_exec_valBy fd₀ hq₀ hk₀ hnn₀ hmssp hv₀
  have hr₁ : KPartRunBy N P P₀ P₁ P₁ ℓ δ₁ mssp fd₁ n₁ Bw₁ σ₁ Pk₁ :=
    kpart_exec_valBy fd₁ hq₁ hk₁ hnn₁ hmssp hv₁
  intro m w b e ν ι hN hb L₀ L₁ Pb₀ Pb₁ β₀ β₁ Rk₀ Rk₁ Z M₀ Y S W' I c hM₀ hZ hbZ hK₀ hK₁ hk₀
    hk₁ ho₀ ho₁ hY hSz hIn hW hWL₀ hWL₁ hc hctx hx hTm hHm hSm hLm hD₀ hD₁ hz hpos₀ hpos₁ hE₀
    hE₁
  obtain ⟨hSw, hSb, hSk₀, hSk₁, hSn₀, hSn₁⟩ := hSz
  obtain ⟨hI₁, hI₂, hI₃, hI₄, hI₅, hI₆⟩ := hIn
  obtain ⟨hW₁, hW₂, hW₃, hW₄, hW₅, hW₆, hW₇⟩ := hW
  have hbw : b ≤ w := hb ▸ card_bdry_le hN
  have hm2 := hN.w2
  have hA : loB m w = 4 * m + 18 * w + 175 := rfl
  have hP₀ : P₀.Nonempty := card_pos.1 hS.2.2.1
  have hP₁ : P₁.Nonempty := card_pos.1 hS.2.2.2.1
  have hx' := hx.reg
  -- 1. the boundary
  obtain ⟨c₁, k₁, e₁, hq₁k, g10, g200, g201, g202, g206, g207, g208, g209, gn₁, gnm₁, grm₁,
    go₁⟩ := bdSet_exec (I := I) c hc (by pomega)
  have hBL : BdLay m w (Z + 0 * M₀) (Z + 1 * M₀) (Z + 2 * M₀) Y (Y + 2 * S) W' (encT N e ν)
      (encH N e ν) (encS P₀ e) :=
    ⟨enc_ends hN, by pomega, by pomega, by pomega, by pomega, by pomega, by pomega, by pomega,
      by pomega, by pomega, by pomega, by pomega, by pomega, by pomega, by pomega⟩
  have hBI : BdIn m w (Z + 0 * M₀) (Z + 1 * M₀) (Z + 2 * M₀) Y (Y + 2 * S) (encT N e ν)
      (encH N e ν) (encS P₀ e) c₁ :=
    ⟨g10, by rw [g200, hctx.r800], by rw [g201, hctx.slot 0 (by omega)],
      by rw [g202, hctx.slot 1 (by omega)], by rw [g206, hctx.slot 2 (by omega)],
      by rw [g207, hctx.r801], by rw [g208, hx' 0 (by omega), zero_mul, add_zero],
      by rw [g209, hx' 2 (by omega)], fun d hd => by rw [gnm₁]; exact hTm d hd,
      fun d hd => by rw [gnm₁]; exact hHm d hd, fun d hd => by rw [gnm₁]; exact hSm d hd⟩
  obtain ⟨c₂, k₂, src, e₂, hq₂k, hsrc, hsl, hm₂, hf₂⟩ :=
    bdryProg_node' (I := I) hN hBL c₁ e₁.wb_right hBI
  rw [← hb] at hsrc hsl
  have hR₂ : ∀ r, (800 ≤ r ∧ r < 900) ∨ 919 ≤ r → c₂.nreg r = c.nreg r := fun r hr => by
    rw [hf₂.nreg r (by pomega), gn₁ r (by pomega) (by pomega)]
  have hm₂' : ∀ a, (a < Y ∨ Y + 3 * S ≤ a) → c₂.nmem a = c.nmem a := fun a ha => by
    rw [hm₂ a (by pomega) (by pomega), gnm₁]
  have hrm₂ : c₂.rmem = c.rmem := by rw [hf₂.rmem, grm₁]
  have hx₂ : XCtx Y S c₂ := hx.of fun r h1 h2 => hR₂ r (by pomega)
  have h802 : c₂.nreg 802 = b := by rw [hR₂ 802 (by pomega), hctx.r802]
  have h807 : c₂.nreg 807 = Z + 4 * M₀ := by rw [hR₂ 807 (by pomega), hctx.slot 4 (by omega)]
  have h808 : c₂.nreg 808 = Z + 5 * M₀ := by rw [hR₂ 808 (by pomega), hctx.slot 5 (by omega)]
  have hpos₀' : ∀ x ∈ bdry N P₀ P₁, c₂.nmem (Pb₀ + ν x) < fd₀.k ∧
      fd₀.Q.tail (fd₀.g (c₂.nmem (Pb₀ + ν x))) = fd₀.j x := fun x hx => by
    rw [hm₂' _ (by pomega)]; exact hpos₀ x hx
  have hpos₁' : ∀ x ∈ bdry N P₀ P₁, c₂.nmem (Pb₁ + ν x) < fd₁.k ∧
      fd₁.Q.tail (fd₁.g (c₂.nmem (Pb₁ + ν x))) = fd₁.j x := fun x hx => by
    rw [hm₂' _ (by pomega)]; exact hpos₁ x hx
  have hδ₀' : ∀ v < w, c₂.rmem (Z + 4 * M₀ + v) = δ₀ (ι v) := fun v hv => by
    rw [hrm₂]; exact hD₀ v hv
  have hδ₁' : ∀ v < w, c₂.rmem (Z + 5 * M₀ + v) = δ₁ (ι v) := fun v hv => by
    rw [hrm₂]; exact hD₁ v hv
  have hE₀' := hE₀.of (d := c₂) (fun i _ => by rw [hrm₂]) (fun i _ => hm₂' _ (by pomega))
  have hE₁' := hE₁.of (d := c₂) (fun i _ => by rw [hrm₂]) (fun i _ => hm₂' _ (by pomega))
  have hlow : ∀ a < Z, c₂.nmem a = 0 := fun a ha => by rw [hm₂' a (by pomega)]; exact hz a ha
  have hKL₀ : ∀ z ≤ 1, KLay b w fd₀.k (Fintype.card (Klein.SrcD fd₀.DQ fd₀.k)) n₀
      (Bw₀ + 16 * (n₀ + 1)) L₀ (Y + 2 * S) Pb₀ (Z + 4 * M₀) (Y + (3 + 5 * z) * S) S β₀ Rk₀ W' :=
    fun z hz => klay_of hz (by pomega) hSb hSk₀ hSn₀ hK₀ hk₀ ho₀ (by pomega) (by pomega) hI₁ hI₃
      hI₅ hW₁ hW₂ hW₄ hW₆ (by pomega) (by pomega)
  have hKL₁ : ∀ z ≤ 1, KLay b w fd₁.k (Fintype.card (Klein.SrcD fd₁.DQ fd₁.k)) n₁
      (Bw₁ + 16 * (n₁ + 1)) L₁ (Y + 2 * S) Pb₁ (Z + 5 * M₀) (Y + (3 + 5 * z) * S) S β₁ Rk₁ W' :=
    fun z hz => klay_of hz (by pomega) hSb hSk₁ hSn₁ hK₁ hk₁ ho₁ (by pomega) (by pomega) hI₂ hI₄
      hI₆ hW₁ hW₃ hW₅ hW₇ (by pomega) (by pomega)
  have e4 : ∀ x, Y + (3 + 5 * 0) * S + S + x = Y + 4 * S + x := fun x => by ring
  have e6 : ∀ x, Y + (3 + 5 * 0) * S + 3 * S + x = Y + 6 * S + x := fun x => by ring
  have e9 : ∀ x, Y + (3 + 5 * 1) * S + S + x = Y + 9 * S + x := fun x => by ring
  have e11 : ∀ x, Y + (3 + 5 * 1) * S + 3 * S + x = Y + 11 * S + x := fun x => by ring
  set p₀ : KP := ⟨fd₀.k, Fintype.card (Klein.SrcD fd₀.DQ fd₀.k), n₀, Bw₀, Pk₀.data.length, β₀,
    Rk₀, Pb₀, L₀, Klein.srcW (fd₀.P'.image fd₀.e) (faceLen fd₀.P' fd₀.e (redLen N ℓ δ₀))⟩
    with hp₀
  set p₁ : KP := ⟨fd₁.k, Fintype.card (Klein.SrcD fd₁.DQ fd₁.k), n₁, Bw₁, Pk₁.data.length, β₁,
    Rk₁, Pb₁, L₁, Klein.srcW (fd₁.P'.image fd₁.e) (faceLen fd₁.P' fd₁.e (redLen N ℓ δ₁))⟩
    with hp₁
  -- 2. the two parts
  obtain ⟨c₃, k₃, γ₀, γ₁, e₃, hk₃, hen₀, hO₀, hcr₀, hF₀, hen₁, hO₁, hcr₁, hF₁, hn₃, hm₃, hr₃,
      ho₃⟩ : ∃ c₃ k₃, ∃ γ₀ γ₁ : ℕ → V,
      Exec I W' (if p₀.Kw ≤ p₁.Kw then kPairOf 0 807 p₀ 1 808 p₁ else kPairOf 1 808 p₁ 0 807 p₀)
        c₂ c₃ k₃ ∧
      k₃ ≤ (3 * (32886 * 2372500000 * P.card * lg P.card) +
            rdCost b L₀ (Fintype.card (Klein.SrcD fd₀.DQ fd₀.k)) + 19 * fd₀.k + 10 * b +
            33 * Fintype.card (Klein.SrcD fd₀.DQ fd₀.k) + 300) +
          (3 * (32886 * 2372500000 * P.card * lg P.card) +
            rdCost b L₁ (Fintype.card (Klein.SrcD fd₁.DQ fd₁.k)) + 19 * fd₁.k + 10 * b +
            33 * Fintype.card (Klein.SrcD fd₁.DQ fd₁.k) + 300) + 14 ∧
      IsEnum b γ₀ (bdry N P₀ P₁) ∧ (∀ x < b, c₃.nmem (Y + 4 * S + x) = ν (γ₀ x)) ∧
      Monge.CrossingO b (fun i i' => (childDDG N mssp P₀ ℓ δ₀ (bdry N P₀ P₁)).len (γ₀ i)
        (γ₀ i')) ∧
      (∀ s < b, ∀ t < b,
        c₃.nmem (Y + 6 * S + (s * b + t)) =
            finB (arcOf (childDDG N mssp P₀ ℓ δ₀ (bdry N P₀ P₁)) γ₀) s t ∧
          c₃.rmem (Y + 6 * S + (s * b + t)) =
            (matOf (childDDG N mssp P₀ ℓ δ₀ (bdry N P₀ P₁)) γ₀ s t : ℝ)) ∧
      IsEnum b γ₁ (bdry N P₀ P₁) ∧ (∀ x < b, c₃.nmem (Y + 9 * S + x) = ν (γ₁ x)) ∧
      Monge.CrossingO b (fun i i' => (childDDG N mssp P₁ ℓ δ₁ (bdry N P₀ P₁)).len (γ₁ i)
        (γ₁ i')) ∧
      (∀ s < b, ∀ t < b,
        c₃.nmem (Y + 11 * S + (s * b + t)) =
            finB (arcOf (childDDG N mssp P₁ ℓ δ₁ (bdry N P₀ P₁)) γ₁) s t ∧
          c₃.rmem (Y + 11 * S + (s * b + t)) =
            (matOf (childDDG N mssp P₁ ℓ δ₁ (bdry N P₀ P₁)) γ₁ s t : ℝ)) ∧
      (∀ r, (800 ≤ r ∧ r < 900) ∨ (919 ≤ r ∧ r < 960) ∨ 967 ≤ r → c₃.nreg r = c₂.nreg r) ∧
      (∀ a, Z ≤ a → a < Y → c₃.nmem a = c₂.nmem a) ∧
      (∀ a, Z ≤ a → a < Y → c₃.rmem a = c₂.rmem a) ∧
      c₃.output = c₂.output := by
    by_cases hKK : Bw₀ + 16 * (n₀ + 1) ≤ Bw₁ + 16 * (n₁ + 1)
    · have hKK' : p₀.Kw ≤ p₁.Kw := hKK
      obtain ⟨c₃, k₃, γ₀, γ₁, e₃, hk₃, hen₀, hO₀, hcr₀, hF₀, hen₁, hO₁, hcr₁, hF₁, hn₃, hm₃,
        hr₃, ho₃⟩ := kpair_execBy hr₀ hr₁ hN hsrc (zf := 0) (zs := 1) (δrf := 807) (δrs := 808)
          (by omega) (by omega) (by omega) (by omega) (by omega) L₀ Pb₀ β₀ Rk₀ (Z + 4 * M₀) L₁
          Pb₁ β₁ Rk₁ (Z + 5 * M₀) Y S W' I c₂ (hKL₀ 0 (by omega)) (hKL₁ 1 (by omega)) hWL₀
          hWL₁ hKK (by pomega) ⟨by pomega, by pomega⟩ ⟨by pomega, by pomega, by pomega⟩
          ⟨by pomega, by pomega⟩ e₂.wb_right h802 hx₂ h807 h808 hsl hpos₀' hpos₁' hδ₀' hδ₁'
          hE₀' hE₁' (fun a ha => by rw [hlow a (by pomega)]; exact Nat.zero_le _)
      refine ⟨c₃, k₃, γ₀, γ₁, by rw [ite_eq_left_of_eq_true _ _ (eq_true hKK')]; exact e₃, hk₃,
        hen₀, fun x hx => by rw [← e4]; exact hO₀ x hx, hcr₀,
        fun s hs t ht => by rw [← e6]; exact hF₀ s hs t ht, hen₁,
        fun x hx => by rw [← e9]; exact hO₁ x hx, hcr₁,
        fun s hs t ht => by rw [← e11]; exact hF₁ s hs t ht, hn₃,
        fun a h1 h2 => hm₃ a (by pomega) (by pomega),
        fun a h1 h2 => hr₃ a (by pomega) (by pomega) (by pomega) (by pomega), ho₃⟩
    · have hKK' : ¬ p₀.Kw ≤ p₁.Kw := hKK
      obtain ⟨c₃, k₃, γ₁, γ₀, e₃, hk₃, hen₁, hO₁, hcr₁, hF₁, hen₀, hO₀, hcr₀, hF₀, hn₃, hm₃,
        hr₃, ho₃⟩ := kpair_execBy hr₁ hr₀ hN hsrc (zf := 1) (zs := 0) (δrf := 808) (δrs := 807)
          (by omega) (by omega) (by omega) (by omega) (by omega) L₁ Pb₁ β₁ Rk₁ (Z + 5 * M₀) L₀
          Pb₀ β₀ Rk₀ (Z + 4 * M₀) Y S W' I c₂ (hKL₁ 1 (by omega)) (hKL₀ 0 (by omega)) hWL₁
          hWL₀ (by omega) (by pomega) ⟨by pomega, by pomega⟩ ⟨by pomega, by pomega, by pomega⟩
          ⟨by pomega, by pomega⟩ e₂.wb_right h802 hx₂ h808 h807 hsl hpos₁' hpos₀' hδ₁' hδ₀'
          hE₁' hE₀' (fun a ha => by rw [hlow a (by pomega)]; exact Nat.zero_le _)
      refine ⟨c₃, k₃, γ₀, γ₁, by rw [ite_eq_right_of_eq_false _ _ (eq_false hKK')]; exact e₃,
        hk₃.trans (le_of_eq (by ring)), hen₀, fun x hx => by rw [← e4]; exact hO₀ x hx, hcr₀,
        fun s hs t ht => by rw [← e6]; exact hF₀ s hs t ht, hen₁,
        fun x hx => by rw [← e9]; exact hO₁ x hx, hcr₁,
        fun s hs t ht => by rw [← e11]; exact hF₁ s hs t ht, hn₃,
        fun a h1 h2 => hm₃ a (by pomega) (by pomega),
        fun a h1 h2 => hr₃ a (by pomega) (by pomega) (by pomega) (by pomega), ho₃⟩
  -- 3. `π`, Bellman–Ford, the Dijkstra half
  have hctx₃ : NCtx m w b Z M₀ c₃ :=
    hctx.of fun r h1 h2 => by rw [hn₃ r (by pomega), hR₂ r (by pomega)]
  have hx₃ : XCtx Y S c₃ := hx.of fun r h1 h2 => by rw [hn₃ r (by pomega), hR₂ r (by pomega)]
  have hm₃' : ∀ a, Z ≤ a → a < Y → c₃.nmem a = c.nmem a := fun a h1 h2 => by
    rw [hm₃ a h1 h2, hm₂' a (by pomega)]
  have hr₃' : ∀ a, Z ≤ a → a < Y → c₃.rmem a = c.rmem a := fun a h1 h2 => by
    rw [hr₃ a h1 h2, hrm₂]
  obtain ⟨c₄, k₄, o, e₄, hk₄, hpot, hstep, ho₄⟩ :=
    rest_exec (I := I) C hfr hmssp hN hP₀ hP₁ ℓ δ₀ δ₁ hδ₀ hδ₁ hen₀ hen₁ hcr₀ hcr₁ hM₀ hZ hbZ hY
      hSw hSb hW₁ c₃ e₃.wb_right hctx₃ hx₃
      (fun d hd => by rw [hm₃' _ (by pomega) (by pomega)]; exact hTm d hd)
      (fun d hd => by rw [hm₃' _ (by pomega) (by pomega)]; exact hHm d hd)
      (fun d hd => by rw [hm₃' _ (by pomega) (by pomega)]; exact hSm d hd)
      (fun d hd => by rw [hr₃' _ (by pomega) (by pomega)]; exact hLm d hd)
      (fun v hv => by rw [hr₃' _ (by pomega) (by pomega)]; exact hD₀ v hv)
      (fun v hv => by rw [hr₃' _ (by pomega) (by pomega)]; exact hD₁ v hv) hO₀ hO₁ hF₀ hF₁
  refine ⟨c₄, k₁ + (k₂ + (k₃ + k₄)), o, Exec.seq e₁ (Exec.seq e₂ (Exec.seq e₃ e₄)), ?_, hpot,
    hstep, by rw [ho₄, ho₃, hf₂.out, go₁]⟩
  clear hstep hpot e₄ e₃ e₂ e₁
  generalize 32886 * 2372500000 * P.card * lg P.card = X at hk₃ ⊢
  pomega

end NegSSSP

end PlanarFlow
