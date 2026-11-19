module

public import PlanarFlow.NegSSSP.NdFullNode

/-!
# The full branch: semantic facts for the node's data

* **`fbExt X f L`**: `f` on `X`, `−(L + 1)` elsewhere (the extended potential of a child, as
  `fbPre` reads it back from a gathered array); **`fbExt_pot`** (a potential of the child's graph
  is still one after the extension), **`fbExt_red`** (the reduced lengths on the child's darts are
  in `[0, 3L]`), **`res_abs`** (the values of an outcome in a frame are within `L`),
  **`fbExt_G`** (the gathered array of `ndB` is `fbExt … + (L + 1)`).
* **`cδ_enum`**: the frame's enumeration `cδ g N P` enumerates `P`; **`msplit_disj`**;
  **`fb_nodeEnc`**: the node's plain encoding (`NodeEnc`) from `ndB`'s numbering.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace NegSSSP

open Finset WordRAM WordRAM.Machine BKMNW

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {N : CombMap D V F}

/-- The extension of `f` from `X` by `−(L + 1)`. -/
def fbExt (X : Finset V) (f : V → ℤ) (L : ℕ) (v : V) : ℤ := if v ∈ X then f v else -((L : ℤ) + 1)

theorem fbExt_pot {P : Finset D} {ℓ : D → ℤ} {f : V → ℤ} (L : ℕ) (hf : (pg N P ℓ).IsPot f) :
    (pg N P ℓ).IsPot (fbExt (verts N P) f L) := by
  intro a
  have ht : N.tail a.1 ∈ verts N P := tail_mem_verts a.2
  have hh : N.head a.1 ∈ verts N P := head_mem_verts a.2
  have := hf a
  simp only [pg, MSSP.pieceGraph] at this ⊢
  unfold fbExt
  rw [if_pos ht, if_pos hh]
  exact this

theorem fbExt_red {P : Finset D} {ℓ : D → ℤ} {f : V → ℤ} {L : ℕ} (hf : (pg N P ℓ).IsPot f)
    (hfL : ∀ v ∈ verts N P, |f v| ≤ L) (hℓ : ∀ x ∈ P, |ℓ x| ≤ L) {x : D} (hx : x ∈ P) :
    0 ≤ redLen N ℓ (fbExt (verts N P) f L) x ∧
      redLen N ℓ (fbExt (verts N P) f L) x < (3 * L + 1 : ℕ) := by
  have ht : N.tail x ∈ verts N P := tail_mem_verts hx
  have hh : N.head x ∈ verts N P := head_mem_verts hx
  have hp := hf ⟨x, hx⟩
  simp only [pg, MSSP.pieceGraph] at hp
  unfold redLen fbExt
  rw [if_pos ht, if_pos hh]
  have a1 := abs_le.1 (hfL _ ht)
  have a2 := abs_le.1 (hfL _ hh)
  have a3 := abs_le.1 (hℓ x hx)
  push_cast
  constructor <;> omega

variable {g : Frame.GIds D V}

/-- **The values of an outcome in a frame are within `L`.** -/
theorem res_abs {L : ℕ} {P : Finset D} {f : V → ℤ} {d e : ℕ} {c : Config}
    (h : Frame.Res g N L P (some f) d e c) : ∀ x ∈ verts N P, |f x| ≤ L := by
  intro x hx
  obtain ⟨-, -, w, ι, -, -, hv, hs⟩ := h
  obtain ⟨v, hv', rfl⟩ := hs x hx
  exact (hv v hv').2.2.2

/-- **The gathered array of `ndB` is the extended potential, offset by `L + 1`.** -/
theorem fbExt_G {X : Finset V} {f : V → ℤ} {L : ℕ} (hfL : ∀ v ∈ X, |f v| ≤ L) {y : V}
    {G : ℕ} (h0 : G = 0 ↔ y ∉ X) (h1 : y ∈ X → G = (f y + L).toNat + 1) :
    (G : ℤ) = fbExt X f L y + (L + 1) ∧ |fbExt X f L y| ≤ L + 1 := by
  unfold fbExt
  by_cases hy : y ∈ X
  · rw [if_pos hy, h1 hy]
    have := abs_le.1 (hfL y hy)
    refine ⟨?_, abs_le.2 ⟨by omega, by omega⟩⟩
    push_cast
    rw [Int.toNat_of_nonneg (by omega)]
    ring
  · rw [if_neg hy, h0.2 hy]
    refine ⟨by push_cast; ring, ?_⟩
    rw [abs_le]; constructor <;> omega

/-- **The frame's enumeration enumerates the piece.** -/
theorem cδ_enum (P : Finset D) : IsEnum P.card (Frame.cδ g N P) P := by
  refine ⟨fun i hi => Frame.cδ_memP hi, fun x hx => ?_, fun i hi i' hi' h => ?_⟩
  · obtain ⟨h1, h2⟩ := Frame.cδ_idxOf (g := g) (N := N) hx
    exact ⟨_, h1, h2⟩
  · have hk := Frame.ck_ge (N := N) P
    exact Frame.cδ_inj (by unfold Frame.ck at hk; omega) (by unfold Frame.ck at hk; omega) h

theorem msplit_disj (P : Finset D) : Disjoint (Frame.msplit g N P).1 (Frame.msplit g N P).2 := by
  unfold Frame.msplit
  rw [disjoint_filter]
  intro x _ h1 h2
  exact h2 h1

/-- **The node's plain encoding from `ndB`'s numbering** (`ν' = ν ∘ g.gv`, `ι v = gInv I[v]`). -/
theorem fb_nodeEnc {P : Finset D} {w : ℕ} {ν : ℕ → ℕ} {I : ℕ → ℕ}
    (hw : w = (verts N P).card)
    (P1 : ∀ x ∈ verts N P, ν (g.gv x) < w ∧ Frame.gInv g N (I (ν (g.gv x))) = x) :
    NodeEnc N (Frame.msplit g N P).1 (Frame.msplit g N P).2 P.card w (Frame.cδ g N P)
      (fun x => ν (g.gv x)) (fun v => Frame.gInv g N (I v)) := by
  have hU := Frame.msplit_union (g := g) (N := N) P
  refine ⟨by rw [hU]; exact cδ_enum P, msplit_disj P,
    fun x hx => (P1 x (by rwa [hU] at hx)).1, fun x hx => (P1 x (by rwa [hU] at hx)).2, ?_⟩
  rw [hw]; exact NTree.card_verts_le P

section Side

open Function Equiv Orbit CombMap Relation PlanarSeparator PlanarSeparator.Map
  PlanarSeparator.StDart Monge.CmpAbs PlanarSeparator.MillerProg

universe u v w

variable {D : Type u} {V : Type v} {F : Type w} [Fintype D] [DecidableEq D] [Fintype V]
  [DecidableEq V] [Fintype F] [DecidableEq F] {N : CombMap D V F}

/-- **The plain arrays of a one-face instance** at `I0` (the hypotheses `hQ…` of `nd_run`). -/
structure FdArr {X : Finset D} {Bs : Finset V} (fd : FaceData N X Bs)
    (σ : fd.DQ ≃ Fin (Fintype.card fd.DQ)) (νv : fd.VQ ≃ Fin (Fintype.card fd.VQ))
    (τ : fd.FQ ≃ Fin (Fintype.card fd.FQ)) (ℓ : D → ℤ) (pot : V → ℤ) (mem : ℕ → ℕ) (I0 : ℕ) :
    Prop where
  rv : ∀ x, mem (I0 + σ x) = σ (fd.Q.rev x)
  nt : ∀ x, mem (I0 + Fintype.card fd.DQ + σ x) = νv (fd.Q.tail x)
  nf : ∀ x, mem (I0 + 2 * Fintype.card fd.DQ + σ x) = τ (fd.Q.face x)
  is : ∀ x, mem (I0 + 3 * Fintype.card fd.DQ + σ x) = if x ∈ fd.P'.image fd.e then 1 else 0
  ln : ∀ x, mem (I0 + 4 * Fintype.card fd.DQ + σ x) = (faceLen fd.P' fd.e (redLen N ℓ pot) x).toNat
  g : ∀ i < fd.k, mem (I0 + 5 * Fintype.card fd.DQ + i) = σ (fd.g i)

/-- **The positions of the sources** at `Pb + ν x` (the hypotheses `hpos` of `nd_run`). -/
def FdPos {X : Finset D} {Bs : Finset V} (fd : FaceData N X Bs) (mem : ℕ → ℕ) (Pb : ℕ)
    (ν : V → ℕ) : Prop :=
  ∀ x ∈ Bs, mem (Pb + ν x) < fd.k ∧ fd.Q.tail (fd.g (mem (Pb + ν x))) = fd.j x

/-- **The one-face instance of a side from the side arrays** (`SideOut`), the arrays copied to
`I0'` and the positions gathered to `Pb + ν x`: for some start `i₀`, the instance
`sideFD … i₀` with numberings `σ`, `νv`, `τ` has its plain arrays at `I0'` and its positions at
`Pb`, and the four size registers hold its sizes. -/
theorem side_data (hM : N.IsPlane) (hrot : N.RotTrans) (hface : N.FaceTrans) {K : Finset D}
    (hKr : K ⊆ reps N) (hK0 : K.Nonempty) (hK : DConn N K) {ψ : V → SVert (kσ N K) (rcl N K)}
    (hψ : ∀ x : SDart (rcl N K), ψ (N.tail x.1) = (kmap N K).vert x)
    {C : (kst N K).SCycle} {Z : Finset (kst N K).Face}
    (hbd : ∀ δ, ((kst N K).face δ ∈ Z ↔ (kst N K).face ((kst N K).α δ) ∈ Z) ↔ ¬ C.Mem δ)
    {Bs : Finset V} (hBs : ∀ b ∈ Bs, b ∈ verts N (side N K Z) ∧ Sum.inl (ψ b) ∈ C.verts)
    {R : Finset D} (hR : Disjoint (verts N R) (verts N K)) {X : Finset D}
    (hX : X = side N K Z ∪ R) {nV : ℕ} {vn : SVert (kσ N K) (rcl N K) ≃ Fin nV} {nF : ℕ}
    {ℓ : D → ℤ} {pot : V → ℤ} {T₀ I0 o : ℕ} {c : Config}
    (hS : SideOut K C Z hbd Bs ψ vn nF ℓ pot T₀ I0 o c) {mem : ℕ → ℕ} {I0' Pb : ℕ}
    {ν : V → ℕ}
    (hcp : ∀ j < 5 * Fintype.card (SDart (discDarts (kst N K) Z)) + C.k,
      mem (I0' + j) = c.nmem (I0 + j))
    (hps : ∀ x ∈ Bs, mem (Pb + ν x) = c.nmem (T₀ + 2 * (nV + nF) + vn (ψ x))) :
    ∃ i₀, ∃ (σ : (sideFD hM hrot hface hKr hK0 hK hψ hbd hBs hR hX i₀).DQ ≃
        Fin (Fintype.card (sideFD hM hrot hface hKr hK0 hK hψ hbd hBs hR hX i₀).DQ))
      (νv : (sideFD hM hrot hface hKr hK0 hK hψ hbd hBs hR hX i₀).VQ ≃
        Fin (Fintype.card (sideFD hM hrot hface hKr hK0 hK hψ hbd hBs hR hX i₀).VQ))
      (τ : (sideFD hM hrot hface hKr hK0 hK hψ hbd hBs hR hX i₀).FQ ≃
        Fin (Fintype.card (sideFD hM hrot hface hKr hK0 hK hψ hbd hBs hR hX i₀).FQ)),
      c.nreg o = Fintype.card (sideFD hM hrot hface hKr hK0 hK hψ hbd hBs hR hX i₀).DQ ∧
      c.nreg (o + 1) = Fintype.card (sideFD hM hrot hface hKr hK0 hK hψ hbd hBs hR hX i₀).VQ ∧
      c.nreg (o + 2) + 1 =
        Fintype.card (sideFD hM hrot hface hKr hK0 hK hψ hbd hBs hR hX i₀).FQ ∧
      c.nreg (o + 3) = (sideFD hM hrot hface hKr hK0 hK hψ hbd hBs hR hX i₀).k ∧
      FdArr (sideFD hM hrot hface hKr hK0 hK hψ hbd hBs hR hX i₀) σ νv τ ℓ pot mem I0' ∧
      FdPos (sideFD hM hrot hface hKr hK0 hK hψ hbd hBs hR hX i₀) mem Pb ν := by
  obtain ⟨i₀, hi₀, hpos, σ₀, νv₀, τ₀, a0, a1, a2, a3, aRV, aNT, aNF, aIS, aLN, aG⟩ := hS
  have hσ : ∀ x, (σ₀ x : ℕ) < Fintype.card (SDart (discDarts (kst N K) Z)) := fun x => (σ₀ x).2
  refine ⟨i₀, σ₀, νv₀, τ₀, a0, a1, a2, a3, ⟨fun x => ?_, fun x => ?_, fun x => ?_,
    fun x => ?_, fun x => ?_, fun i hi => ?_⟩, fun x hx => ?_⟩
  · rw [hcp _ (by have := hσ x; omega)]; exact aRV x
  · have := hσ x
    have e := hcp (Fintype.card (SDart (discDarts (kst N K) Z)) + σ₀ x) (by omega)
    rw [← Nat.add_assoc, ← Nat.add_assoc] at e
    exact e.trans (aNT x)
  · have := hσ x
    have e := hcp (2 * Fintype.card (SDart (discDarts (kst N K) Z)) + σ₀ x) (by omega)
    rw [← Nat.add_assoc, ← Nat.add_assoc] at e
    exact e.trans (aNF x)
  · have := hσ x
    have e := hcp (3 * Fintype.card (SDart (discDarts (kst N K) Z)) + σ₀ x) (by omega)
    rw [← Nat.add_assoc, ← Nat.add_assoc] at e
    exact e.trans (aIS x)
  · have := hσ x
    have e := hcp (4 * Fintype.card (SDart (discDarts (kst N K) Z)) + σ₀ x) (by omega)
    rw [← Nat.add_assoc, ← Nat.add_assoc] at e
    exact e.trans (aLN x)
  · have hi' : i < C.k := hi
    have e := hcp (5 * Fintype.card (SDart (discDarts (kst N K) Z)) + i) (by omega)
    rw [← Nat.add_assoc, ← Nat.add_assoc] at e
    exact e.trans (aG i hi')
  · obtain ⟨h1, h2⟩ := hpos x hx
    rw [hps x hx]
    exact sideFD_pos hM hrot hface hKr hK0 hK hψ hbd hBs hR hX i₀ h1 h2

/-- **The weight bound of an instance from its plain arrays** (`pw_srcW`). -/
theorem fdArr_srcW {X : Finset D} {Bs : Finset V} {fd : FaceData N X Bs}
    {σ : fd.DQ ≃ Fin (Fintype.card fd.DQ)} {νv : fd.VQ ≃ Fin (Fintype.card fd.VQ)}
    {τ : fd.FQ ≃ Fin (Fintype.card fd.FQ)} {ℓ : D → ℤ} {pot : V → ℤ} {mem : ℕ → ℕ} {I0 : ℕ}
    (h : FdArr fd σ νv τ ℓ pot mem I0) :
    1 + pwS mem (I0 + 3 * Fintype.card fd.DQ) (I0 + 4 * Fintype.card fd.DQ)
      (Fintype.card fd.DQ) =
      (Klein.srcW (fd.P'.image fd.e) (faceLen fd.P' fd.e (redLen N ℓ pot))).toNat :=
  pw_srcW σ _ _ (fun x => faceLen_nonneg _ _ _ x) mem _ _ h.is h.ln

end Side

/-- **A residue of an integer within `B` of `0`.** -/
theorem res_near {z : ℤ} {M B v : ℕ} (hv : (v : ℤ) = z % (M : ℤ)) (hz : |z| ≤ B) (hBM : B < M) :
    v < M ∧ (v ≤ B ∨ M ≤ v + B) := by
  have hM : (0 : ℤ) < M := by omega
  have h1 := Int.emod_nonneg z hM.ne'
  have h2 := Int.emod_lt_of_pos z hM
  have hz' := abs_le.1 hz
  refine ⟨by omega, ?_⟩
  rcases le_or_gt 0 z with h | h
  · left
    have : z % M = z := Int.emod_eq_of_lt h (by omega)
    omega
  · right
    have e1 : (z + M) % M = z % M := by simp
    have e2 : (z + M) % M = z + M := Int.emod_eq_of_lt (by omega) (by omega)
    omega

/-- **`Z = fbZ …` is above every lower bound of the node** (`node_exec_fixedD`). -/
theorem fbZ_bounds (B₀ k m w b : ℕ) (p₀ p₁ : FeP) :
    loB m w ≤ fbZ B₀ k m w b p₀ p₁ ∧ bfWP b < fbZ B₀ k m w b p₀ p₁ ∧
    2 * p₀.Kw + 1 < fbZ B₀ k m w b p₀ p₁ ∧ 2 * p₁.Kw + 1 < fbZ B₀ k m w b p₀ p₁ ∧
    p₀.NN + p₀.k * p₀.k ≤ fbZ B₀ k m w b p₀ p₁ ∧ p₁.NN + p₁.k * p₁.k ≤ fbZ B₀ k m w b p₀ p₁ ∧
    B₀ + 66 * k + 320 ≤ fbZ B₀ k m w b p₀ p₁ := by
  have K0 : 2 * p₀.Kw + 1 = 28 * (p₀.nD + 8 * p₀.k) +
      48 * (2 * (p₀.nD + 8 * p₀.k) + 2 * (p₀.nV + 2 * p₀.k) + 2 * (p₀.nF + 2 * p₀.k)) +
      6 * p₀.k + 2 * (p₀.k * p₀.k) + 47 := by
    simp only [FeP.Kw, FeP.Bw, Klein.kBL, Klein.aOUT, FeP.NN, FeP.AE, FeP.A, FeP.N, FeP.FN]; ring
  have K1 : 2 * p₁.Kw + 1 = 28 * (p₁.nD + 8 * p₁.k) +
      48 * (2 * (p₁.nD + 8 * p₁.k) + 2 * (p₁.nV + 2 * p₁.k) + 2 * (p₁.nF + 2 * p₁.k)) +
      6 * p₁.k + 2 * (p₁.k * p₁.k) + 47 := by
    simp only [FeP.Kw, FeP.Bw, Klein.kBL, Klein.aOUT, FeP.NN, FeP.AE, FeP.A, FeP.N, FeP.FN]; ring
  have N0 : p₀.NN = 2 * (p₀.nD + 8 * p₀.k) + 2 * (p₀.nV + 2 * p₀.k) + 2 * (p₀.nF + 2 * p₀.k) := by
    simp only [FeP.NN, FeP.AE, FeP.A, FeP.N, FeP.FN]; ring
  have N1 : p₁.NN = 2 * (p₁.nD + 8 * p₁.k) + 2 * (p₁.nV + 2 * p₁.k) + 2 * (p₁.nF + 2 * p₁.k) := by
    simp only [FeP.NN, FeP.AE, FeP.A, FeP.N, FeP.FN]; ring
  have hZ : fbZ B₀ k m w b p₀ p₁ = B₀ + 66 * k + 4 * m + 18 * w + 8 * (b * b) + 14 * b +
      28 * (p₀.nD + 8 * p₀.k) +
      49 * (2 * (p₀.nD + 8 * p₀.k) + 2 * (p₀.nV + 2 * p₀.k) + 2 * (p₀.nF + 2 * p₀.k)) +
      6 * p₀.k + 3 * (p₀.k * p₀.k) + 28 * (p₁.nD + 8 * p₁.k) +
      49 * (2 * (p₁.nD + 8 * p₁.k) + 2 * (p₁.nV + 2 * p₁.k) + 2 * (p₁.nF + 2 * p₁.k)) +
      6 * p₁.k + 3 * (p₁.k * p₁.k) + 320 := rfl
  rw [hZ, K0, K1, N0, N1]
  unfold loB bfWP
  generalize p₀.k * p₀.k = q0
  generalize p₁.k * p₁.k = q1
  generalize b * b = bb
  generalize p₀.nD + 8 * p₀.k = x0
  generalize p₁.nD + 8 * p₁.k = x1
  generalize 2 * x0 + 2 * (p₀.nV + 2 * p₀.k) + 2 * (p₀.nF + 2 * p₀.k) = y0
  generalize 2 * x1 + 2 * (p₁.nV + 2 * p₁.k) + 2 * (p₁.nF + 2 * p₁.k) = y1
  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩

end NegSSSP

end PlanarFlow
