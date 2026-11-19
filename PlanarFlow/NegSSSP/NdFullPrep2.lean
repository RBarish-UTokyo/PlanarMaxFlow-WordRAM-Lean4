module

public import PlanarFlow.NegSSSP.NdFullPrep

/-!
# The full branch: the side arrays from the split's data

**`fs_p2`**: from the end of `fs_p1` (the split's data `BigOut` of the large component
`K = pcomp N P x₁`, `ndB`'s numbering and gathered arrays), the cut `A₀` with
`msplit g N P = cutPair P K A₀` (`msplit_cut`), and the run of `fbA` (`fbA_exec`): the side
arrays of both sides with the extended potentials `fbExt` of the children's outcomes.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace NegSSSP

open Finset Function Equiv Orbit CombMap Relation PlanarSeparator PlanarSeparator.Map
  PlanarSeparator.StDart BKMNW WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs
  Monge.CmpAbs PlanarSeparator.MillerProg

theorem sq_le_self {q m : ℕ} (h : q ^ 2 ≤ 1200 * m) (hm : 1200 < m) : q ≤ m := by
  by_contra hq
  push_neg at hq
  have h1 : (m + 1) * (m + 1) ≤ q * q := Nat.mul_le_mul hq hq
  have h2 : 1201 * m ≤ m * m := Nat.mul_le_mul_right _ (by omega)
  rw [pow_two] at h
  nlinarith

universe u v w

variable {P : Input} {W : ℕ}

variable {D : Type u} {V : Type v} {F : Type w} [Fintype D] [DecidableEq D] [Fintype V]
  [DecidableEq V] [Fintype F] [DecidableEq F] {N : CombMap D V F} {g : Frame.GIds D V}

set_option maxHeartbeats 16000000 in
open Classical in
/-- **The side arrays from the split's data** (see the module docstring). -/
theorem fs_p2 (hM : N.IsPlane) (hrot : N.RotTrans) (hface : N.FaceTrans) {ℓ : D → ℤ}
    {L n : ℕ} {Q : Finset D} {d e h w : ℕ} {ν' : ℕ → ℕ} {f₀ f₁ : V → ℤ} {x₁ : D}
    (c : Config) (hc : WordsBounded W c) (hQr : Q ⊆ reps N)
    (hin : Frame.InP g N ℓ L (n + 1) Q d e c)
    (hp0 : (pg N (Frame.msplit g N Q).1 ℓ).IsPot f₀) (hp1 : (pg N (Frame.msplit g N Q).2 ℓ).IsPot f₁)
    (hf0 : ∀ x ∈ verts N (Frame.msplit g N Q).1, |f₀ x| ≤ L)
    (hf1 : ∀ x ∈ verts N (Frame.msplit g N Q).2, |f₁ x| ≤ L) (hℓ : ∀ x, |ℓ x| ≤ L)
    (r03 : c.nreg 3003 = h) (r04 : c.nreg 3004 = d) (r75 : c.nreg 2475 = Frame.ck N Q)
    (r74 : c.nreg 2474 = Q.card) (r64 : c.nreg 2464 = w)
    (r72 : c.nreg 2972 = Frame.spB0 (Frame.ck N Q)) (hwv : w = (verts N Q).card)
    (P1 : ∀ x ∈ verts N Q, ν' (g.gv x) < w ∧
      Frame.gInv g N (c.nmem (h + 2 * Frame.ck N Q + ν' (g.gv x))) = x)
    (hT : ∀ a < Q.card, c.nmem (h + a) = ν' (g.gv (N.tail (Frame.cδ g N Q a))))
    (hH : ∀ a < Q.card, c.nmem (h + Frame.ck N Q + a) = ν' (g.gv (N.head (Frame.cδ g N Q a))))
    (hG₀ : ∀ v < w, (c.nmem (h + 4 * Frame.ck N Q + v) : ℤ) =
        fbExt (verts N (Frame.msplit g N Q).1) f₀ L
          (Frame.gInv g N (c.nmem (h + 2 * Frame.ck N Q + v))) + (L + 1) ∧
      |fbExt (verts N (Frame.msplit g N Q).1) f₀ L
          (Frame.gInv g N (c.nmem (h + 2 * Frame.ck N Q + v)))| ≤ L + 1)
    (hG₁ : ∀ v < w, (c.nmem (h + 6 * Frame.ck N Q + v) : ℤ) =
        fbExt (verts N (Frame.msplit g N Q).2) f₁ L
          (Frame.gInv g N (c.nmem (h + 2 * Frame.ck N Q + v))) + (L + 1) ∧
      |fbExt (verts N (Frame.msplit g N Q).2) f₁ L
          (Frame.gInv g N (c.nmem (h + 2 * Frame.ck N Q + v)))| ≤ L + 1)
    (hx₁ : x₁ ∈ Q) (hbx : 3 * Q.card / 4 < (pcomp N Q x₁).card)
    (hBO : BigOut N Q Q.card (Frame.ck N Q) (Frame.cδ g N Q) (Frame.spB0 (Frame.ck N Q)) x₁ c)
    (hSp : ∀ a ≤ Frame.spWs (Frame.ck N Q), c.nmem a = (Frame.spFin g N Q).nmem a)
    (hbig : 1000000 < Q.card)
    (hdh : d + 4 + 5 * Frame.ck N Q + Q.card ≤ h) (hB : Frame.spWs (Frame.ck N Q) < d)
    (hW : h + 150 * Frame.ck N Q ≤ W) (hLW : 3 * (3 * L + 1) + 2 * L + 2 ≤ W)
    (h9600 : 9600 ≤ W) :
    ∃ (A₀ : Finset D) (nV nF m' : ℕ) (cn : SDart (rcl N (pcomp N Q x₁)) ≃ Fin m')
      (vn : SVert (kσ N (pcomp N Q x₁)) (rcl N (pcomp N Q x₁)) ≃ Fin nV)
      (fn : (kmap N (pcomp N Q x₁)).Face ≃ Fin nF)
      (ψ : V → SVert (kσ N (pcomp N Q x₁)) (rcl N (pcomp N Q x₁)))
      (C : (kst N (pcomp N Q x₁)).SCycle) (Z : Finset (kst N (pcomp N Q x₁)).Face)
      (hbd₀ : ∀ δ, ((kst N (pcomp N Q x₁)).face δ ∈ Z ↔
        (kst N (pcomp N Q x₁)).face ((kst N (pcomp N Q x₁)).α δ) ∈ Z) ↔ ¬ C.Mem δ)
      (hbd₁ : ∀ δ, ((kst N (pcomp N Q x₁)).face δ ∈ Zᶜ ↔
        (kst N (pcomp N Q x₁)).face ((kst N (pcomp N Q x₁)).α δ) ∈ Zᶜ) ↔ ¬ C.Mem δ),
      CutOK N (pcomp N Q x₁) A₀ ∧ Frame.msplit g N Q = cutPair Q (pcomp N Q x₁) A₀ ∧
      side N (pcomp N Q x₁) Z = A₀ ∧ side N (pcomp N Q x₁) Zᶜ = pcomp N Q x₁ \ A₀ ∧
      (∀ x : SDart (rcl N (pcomp N Q x₁)), ψ (N.tail x.1) = (kmap N (pcomp N Q x₁)).vert x) ∧
      (∀ b ∈ bdry N A₀ (pcomp N Q x₁ \ A₀), Sum.inl (ψ b) ∈ C.verts) ∧
      C.k ^ 2 ≤ 1200 * Q.card ∧ C.k ≤ Frame.ck N Q ∧ m' ≤ Frame.ck N Q ∧
      nV + nF ≤ 2 * Frame.ck N Q ∧
      Enc (kmap N (pcomp N Q x₁)) cn vn fn c.nmem (Frame.spB0 (Frame.ck N Q) + 28 * Frame.ck N Q + 3)
        (Frame.spB0 (Frame.ck N Q) + 28 * Frame.ck N Q + 3 + m')
        (Frame.spB0 (Frame.ck N Q) + 28 * Frame.ck N Q + 3 + 2 * m')
        (Frame.spB0 (Frame.ck N Q) + 28 * Frame.ck N Q + 3 + 3 * m')
        (Frame.spB0 (Frame.ck N Q) + 28 * Frame.ck N Q + 3 + 4 * m') ∧
      (∀ i < Frame.ck N Q, ∀ hm : Frame.cδ g N Q i ∈ rcl N (pcomp N Q x₁),
        c.nmem (Frame.spB0 (Frame.ck N Q) + 25 * Frame.ck N Q + 3 + i) = cn ⟨Frame.cδ g N Q i, hm⟩) ∧
      (∀ x < Q.card, (c.nmem (Frame.spB0 (Frame.ck N Q) + 33 * Frame.ck N Q + 3 + x) ≠ 0 ↔
        Frame.cδ g N Q x ∈ pcomp N Q x₁)) ∧
      (∀ x < Q.card, c.nmem (Frame.spB0 (Frame.ck N Q) + 41 * Frame.ck N Q + 4 + x) =
        if Frame.cδ g N Q x ∈ (cutPair Q (pcomp N Q x₁) A₀).1 then 0 else 1) ∧
      c.nreg 960 = m' ∧ c.nreg 961 = nV ∧ c.nreg 962 = nF ∧
      ∃ c' t, Exec P W fbA c c' t ∧
        t ≤ fbPreCost (Frame.ck N Q) + 2 * (33 * Q.card + 405 * m' + 13 * (nV + nF) +
          22 * C.k + 155) ∧
        FbRegs c' h d (Frame.ck N Q) (Frame.spB0 (Frame.ck N Q)) m' L ∧
        SideOut (pcomp N Q x₁) C Z hbd₀ (bdry N A₀ (pcomp N Q x₁ \ A₀)) ψ vn nF ℓ
          (fbExt (verts N (Frame.msplit g N Q).1) f₀ L) (h + 20 * Frame.ck N Q)
          (h + 50 * Frame.ck N Q) 2240 c' ∧
        SideOut (pcomp N Q x₁) C Zᶜ hbd₁ (bdry N A₀ (pcomp N Q x₁ \ A₀)) ψ vn nF ℓ
          (fbExt (verts N (Frame.msplit g N Q).2) f₁ L) (h + 80 * Frame.ck N Q)
          (h + 110 * Frame.ck N Q) 2244 c' ∧
        (∀ i < 2 * Frame.ck N Q, c'.nmem (h + 10 * Frame.ck N Q + i) = i) ∧
        (∀ a, (a < h + 10 * Frame.ck N Q ∨ h + 126 * Frame.ck N Q ≤ a) → c'.nmem a = c.nmem a) ∧
        (∀ r, r ≠ 10 → (r < 300 ∨ 318 < r) → (r < 800 ∨ 840 < r) → (r < 2100 ∨
          (2248 ≤ r ∧ r < 2550) ∨ (2593 < r ∧ r < 2750) ∨ 2850 < r) → c'.nreg r = c.nreg r) ∧
        c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨A₀, hcut, hsideA, nV, nF, q, νb, hνb, hVF, hq, -, -, m', cn, vn, fn, ψ, C, Z, hm', -,
    hqk, hψ, hsZ, hsZc, hbd₀, hbd₁, hBsC, hE, hz₀, hz₁, hXm, hFm, r960, r961, r962, -⟩ := hBO
  have hKQ : (pcomp N Q x₁) ⊆ Q := pcomp_subset Q x₁
  have hRd : Disjoint (verts N (Q \ (pcomp N Q x₁))) (verts N (pcomp N Q x₁)) := disjoint_verts_pcomp Q x₁
  have hmk := Frame.ck_ge (N := N) Q
  have hcutEq : Frame.msplit g N Q = cutPair Q (pcomp N Q x₁) A₀ :=
    Frame.msplit_cut hbig hKQ hRd hbx hcut fun x hx => by
      rw [← hSp _ (by unfold Frame.spWs; omega)]; exact hsideA x hx
  obtain ⟨R₀, R₁, e0, e1, -, -⟩ := cut_parts Q (pcomp N Q x₁) A₀
  have hA0 : A₀ ⊆ (Frame.msplit g N Q).1 := by rw [hcutEq, e0]; exact subset_union_left
  have hA1 : (pcomp N Q x₁) \ A₀ ⊆ (Frame.msplit g N Q).2 := by rw [hcutEq, e1]; exact subset_union_left
  have hqsq : q ^ 2 ≤ 1200 * Q.card := cut_k_sq hbig hKQ hq
  have hCk : C.k ≤ Frame.ck N Q := by
    have := (sq_le_self hqsq (by omega)).trans hmk; omega
  have hen := hin.en
  unfold Frame.fsz at hen
  have hw2 : w ≤ 2 * Frame.ck N Q := by
    have := NTree.card_verts_le (N := N) Q; omega
  obtain ⟨c', t, ex, ht, hR, hS0, hS1, hid, hmem, hreg, hrr, hrm, ho⟩ :=
    fbA_exec (P := P) hrot (hQr.trans' hKQ |>.trans le_rfl) hbd₀ hbd₁ hBsC
      (Frame.penc_canon (g := g) Q) hKQ ℓ (fbExt (verts N (Frame.msplit g N Q).1) f₀ L)
      (fbExt (verts N (Frame.msplit g N Q).2) f₁ L) (fun x => ν' (g.gv x))
      (fun v => Frame.gInv g N (c.nmem (h + 2 * Frame.ck N Q + v))) cn vn fn c hc r03 r04 r75
      r74 r64 r72 r960 r961 r962 hin.rL (fun i hi => hin.ln i hi) (fun i _ => hℓ _)
      (fun i hi => by
        have hx := tail_mem_verts (N := N) (Frame.cδ_memP (g := g) (N := N) hi)
        exact ⟨hT i hi, (P1 _ hx).1, (P1 _ hx).2⟩)
      (fun i hi => by
        have hx := head_mem_verts (N := N) (Frame.cδ_memP (g := g) (N := N) hi)
        exact ⟨hH i hi, (P1 _ hx).1, (P1 _ hx).2⟩)
      hG₀ hG₁ hE hz₀ hz₁ hXm hFm
      (fun x hx => fbExt_red hp0 hf0 (fun y _ => hℓ y) (hA0 (hsZ ▸ hx)))
      (fun x hx => fbExt_red hp1 hf1 (fun y _ => hℓ y) (hA1 (hsZc ▸ hx)))
      hCk hmk hw2 hm' hVF hdh (by unfold Frame.spWs at hB; unfold Frame.ck at hB ⊢; omega) hW
      (by unfold Frame.ck at hmk; omega) hLW h9600
  exact ⟨A₀, nV, nF, m', cn, vn, fn, ψ, C, Z, hbd₀, hbd₁, hcut, hcutEq, hsZ, hsZc, hψ, hBsC,
    by rw [← hqk]; exact hqsq, hCk, hm', hVF, hE, hXm, hFm, hsideA, r960, r961, r962, c', t, ex, ht, hR, hS0,
    hS1, hid, hmem, hreg, hrr, hrm, ho⟩

end NegSSSP

end PlanarFlow
