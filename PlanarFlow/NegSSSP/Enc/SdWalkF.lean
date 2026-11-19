module

public import PlanarFlow.NegSSSP.Enc.SdWalk

/-!
# The walk of a side with its register frame

**`sdWalk_exec'`**: the statement of `sdWalk_exec` (same program `sdWalkProg`, same bound) with,
in addition, the registers it keeps: all but `300 … 314`, `820 … 840`, `2558`, `2559` and
`2562 … 2593`. The proof is that of `sdWalk_exec`, keeping the frame of `sdSide_exec`.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace PlanarFlow

namespace NegSSSP

open Finset Function Equiv Orbit CombMap Relation PlanarSeparator PlanarSeparator.Map
  PlanarSeparator.StDart BKMNW WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs
  Monge.CmpAbs PlanarSeparator.MillerProg

universe u v w

variable {P : Input} {W : ℕ}

section Side

variable {D : Type u} {V : Type v} {F : Type w} [Fintype D] [DecidableEq D] [Fintype V]
  [DecidableEq V] [Fintype F] [DecidableEq F] {N : CombMap D V F}
variable {K : Finset D} {C : (kst N K).SCycle} {Z : Finset (kst N K).Face}

set_option maxHeartbeats 4000000 in
/-- **The walk of a side and the plain arrays of its instance, as one run.** See the module
docstring. -/
theorem sdWalk_exec' (hrot : N.RotTrans) (hKr : K ⊆ reps N) {ψ : V → SVert (kσ N K) (rcl N K)}
    (hbd : ∀ δ, ((kst N K).face δ ∈ Z ↔ (kst N K).face ((kst N K).α δ) ∈ Z) ↔ ¬ C.Mem δ)
    {Bs : Finset V} (hBs : ∀ b ∈ Bs, Sum.inl (ψ b) ∈ C.verts) (ℓ : D → ℤ)
    {m nV nF : ℕ} (c : SDart (rcl N K) ≃ Fin m) (vn : SVert (kσ N K) (rcl N K) ≃ Fin nV)
    (fn : (kmap N K).Face ≃ Fin nF) {bα bφ bφi bvn bfn bz sv T₀ bA bV bK bL S I0 : ℕ}
    (c₀ : Config) (hw : WordsBounded W c₀)
    (hE : Enc (kmap N K) c vn fn c₀.nmem bα bφ bφi bvn bfn)
    (hz : ∀ x, ((kst N K).face (old x) ∈ Z ↔ c₀.nmem (bz + c x) = sv))
    (hKB : ∀ x, c₀.nmem (bK + c x) = if x.1 ∈ K then 1 else 0)
    (hLP : ∀ x : SDart (rcl N K), x.1 ∈ K → c₀.nmem (bL + c x) = (ℓ x.1).toNat)
    (hlay : bα + m ≤ T₀ ∧ bφ + m ≤ T₀ ∧ bφi + m ≤ T₀ ∧ bvn + m ≤ T₀ ∧ bfn + m ≤ T₀ ∧
      bz + m ≤ T₀ ∧ bK + m ≤ T₀ ∧ bL + m ≤ T₀)
    (h10 : c₀.nreg 10 = 1) (h800 : c₀.nreg 800 = m) (h801 : c₀.nreg 801 = bα)
    (h802 : c₀.nreg 802 = bφ) (h803 : c₀.nreg 803 = bφi) (h804 : c₀.nreg 804 = bvn)
    (h805 : c₀.nreg 805 = bfn) (h806 : c₀.nreg 806 = bz) (h807 : c₀.nreg 807 = nV)
    (h808 : c₀.nreg 808 = nF) (h809 : c₀.nreg 809 = sv) (h810 : c₀.nreg 810 = T₀)
    (hR : StR m bα bφ bφi bA bvn bfn bV nV c₀)
    (r50 : c₀.nreg 2550 = m) (r51 : c₀.nreg 2551 = bz) (r52 : c₀.nreg 2552 = sv)
    (r53 : c₀.nreg 2553 = bA) (r54 : c₀.nreg 2554 = bV) (r55 : c₀.nreg 2555 = nV + nF)
    (r56 : c₀.nreg 2556 = bK) (r57 : c₀.nreg 2557 = bL) (r60 : c₀.nreg 2560 = S)
    (r61 : c₀.nreg 2561 = I0)
    (l1 : T₀ + 3 * (nV + nF) + 6 * m + C.k ≤ bA) (l2 : bA + 3 * m ≤ bV) (l3 : bV + 3 * m ≤ S)
    (l4 : S + 7 * m + 2 * (nV + nF) ≤ I0) (hW : I0 + 18 * m + C.k + 5 ≤ W) :
    ∃ c' t, Exec P W sdWalkProg c₀ c' t ∧
      t ≤ 400 * m + 13 * (nV + nF) + 22 * C.k + 75 ∧ ∃ i₀ < C.k,
      (∀ b ∈ Bs, c'.nmem (T₀ + 2 * (nV + nF) + vn (ψ b)) < C.k ∧
        (kst N K).vert ((discCyc C Z).d ((i₀ + c'.nmem (T₀ + 2 * (nV + nF) + vn (ψ b))) %
          C.k)) = .inl (ψ b)) ∧
      ∃ (σ₀ : SDart (discDarts (kst N K) Z) ≃ Fin (Fintype.card (SDart (discDarts (kst N K) Z))))
        (νv₀ : SVert (dσ (kst N K) Z) (discDarts (kst N K) Z) ≃
          Fin (Fintype.card (SVert (dσ (kst N K) Z) (discDarts (kst N K) Z))))
        (τ₀ : SFace (dσ (kst N K) Z) (discDarts (kst N K) Z) (revPerm (combOfSep (kst N K))) ≃
          Fin (Fintype.card (SFace (dσ (kst N K) Z) (discDarts (kst N K) Z)
            (revPerm (combOfSep (kst N K)))))),
        c'.nreg 2580 = Fintype.card (SDart (discDarts (kst N K) Z)) ∧
        c'.nreg 2593 = Fintype.card (SVert (dσ (kst N K) Z) (discDarts (kst N K) Z)) ∧
        c'.nreg 2581 + 1 = Fintype.card (SFace (dσ (kst N K) Z) (discDarts (kst N K) Z)
          (revPerm (combOfSep (kst N K)))) ∧
        (∀ d, c'.nmem (I0 + σ₀ d) = σ₀ ((discMap (kst N K) Z).rev d)) ∧
        (∀ d, c'.nmem (I0 + Fintype.card (SDart (discDarts (kst N K) Z)) + σ₀ d) =
          νv₀ ((discMap (kst N K) Z).tail d)) ∧
        (∀ d, c'.nmem (I0 + 2 * Fintype.card (SDart (discDarts (kst N K) Z)) + σ₀ d) =
          τ₀ ((discMap (kst N K) Z).face d)) ∧
        (∀ d, c'.nmem (I0 + 3 * Fintype.card (SDart (discDarts (kst N K) Z)) + σ₀ d) =
          if d ∈ (side N K Z).image (sideE hbd) then 1 else 0) ∧
        (∀ d, c'.nmem (I0 + 4 * Fintype.card (SDart (discDarts (kst N K) Z)) + σ₀ d) =
          (faceLen (side N K Z) (sideE hbd) ℓ d).toNat) ∧
        (∀ i < C.k, c'.nmem (I0 + 5 * Fintype.card (SDart (discDarts (kst N K) Z)) + i) =
          σ₀ (discFace hbd i₀ i)) ∧
        (∀ a, a < T₀ ∨ I0 + 5 * Fintype.card (SDart (discDarts (kst N K) Z)) + C.k ≤ a →
          c'.nmem a = c₀.nmem a) ∧
        (∀ r, (r < 300 ∨ (314 < r ∧ r < 820) ∨ (840 < r ∧ r < 2558) ∨ (2559 < r ∧ r < 2562) ∨
          2593 < r) → c'.nreg r = c₀.nreg r) ∧
        c'.rreg = c₀.rreg ∧ c'.rmem = c₀.rmem ∧ c'.output = c₀.output := by
  obtain ⟨l1', l2', l3', l4', l5', l6', l7', l8'⟩ := hlay
  -- the walk
  obtain ⟨c₁, t₁, e₁, ht₁, r829, fr₁, wm₁, i₀, hi₀, wC, wP⟩ :=
    faceWalk_side (P := P) (W := W) hrot hKr hbd hBs c vn fn hE hz
      ⟨l1', l2', l3', l4', l5', l6'⟩ (by omega) hw h10 h800 h801 h802 h803 h804 h805 h806 h807
      h808 h809 h810
  have F₁ : ∀ r, r < 820 ∨ 840 < r → c₁.nreg r = c₀.nreg r := fr₁.nreg
  have M₁ : ∀ a, a < T₀ → c₁.nmem a = c₀.nmem a := fun a h => wm₁ a (Or.inl h)
  -- the registers of the arrays
  obtain ⟨c₂, t₂, e₂, ht₂, g58, g59, gr₂, gm₂, grr₂, grm₂, go₂⟩ := sdWSet_exec (P := P) c₁
    e₁.wb_right (nV := nV) (nF := nF) (T₀ := T₀) ((F₁ 807 (by omega)).trans h807)
    ((F₁ 808 (by omega)).trans h808) ((F₁ 810 (by omega)).trans h810) r829 (by omega)
  have F₂ : ∀ r, (r < 820 ∨ 840 < r) → r ≠ 2558 → r ≠ 2559 → c₂.nreg r = c₀.nreg r :=
    fun r h1 h2 h3 => (gr₂ r h2 h3).trans (F₁ r h1)
  have M₂ : ∀ a, a < T₀ → c₂.nmem a = c₀.nmem a := fun a h => by rw [gm₂, M₁ a h]
  have hR₂ : StR m bα bφ bφi bA bvn bfn bV nV c₂ :=
    ⟨(F₂ 301 (by omega) (by omega) (by omega)).trans hR.r301,
      (F₂ 302 (by omega) (by omega) (by omega)).trans hR.r302,
      (F₂ 303 (by omega) (by omega) (by omega)).trans hR.r303,
      (F₂ 304 (by omega) (by omega) (by omega)).trans hR.r304,
      (F₂ 305 (by omega) (by omega) (by omega)).trans hR.r305,
      (F₂ 306 (by omega) (by omega) (by omega)).trans hR.r306,
      (F₂ 307 (by omega) (by omega) (by omega)).trans hR.r307,
      (F₂ 308 (by omega) (by omega) (by omega)).trans hR.r308,
      (F₂ 315 (by omega) (by omega) (by omega)).trans hR.r315,
      (F₂ 316 (by omega) (by omega) (by omega)).trans hR.r316,
      (F₂ 317 (by omega) (by omega) (by omega)).trans hR.r317,
      (F₂ 318 (by omega) (by omega) (by omega)).trans hR.r318⟩
  have hE₂ : Enc (kmap N K) c vn fn c₂.nmem bα bφ bφi bvn bfn :=
    ⟨fun d => by rw [M₂ _ (by have := (c d).2; omega)]; exact hE.α d,
      fun d => by rw [M₂ _ (by have := (c d).2; omega)]; exact hE.φ d,
      fun d => by rw [M₂ _ (by have := (c d).2; omega)]; exact hE.φi d,
      fun d => by rw [M₂ _ (by have := (c d).2; omega)]; exact hE.vn d,
      fun d => by rw [M₂ _ (by have := (c d).2; omega)]; exact hE.fn d⟩
  -- the arrays
  obtain ⟨c₃, t₃, e₃, ht₃, σ₀, νv₀, τ₀, a80, a93, a81, aRV, aNT, aNF, aIS, aLN, aG, am₃, af₃, ar₃,
      arm₃, ao₃⟩ :=
    sdSide_exec (P := P) (C := C) (Z := Z) hrot hKr hbd i₀ ℓ c vn fn (bA := bA) (bV := bV)
      (bz := bz) (sv := sv) (bK := bK) (bL := bL) (bW := T₀ + 3 * (nV + nF)) (S := S) (I0 := I0)
      c₂ e₂.wb_right hE₂ hR₂
      (fun x => by rw [M₂ _ (by have := (c x).2; omega)]; exact hz x)
      (fun x => by rw [M₂ _ (by have := (c x).2; omega)]; exact hKB x)
      (fun x hx => by rw [M₂ _ (by have := (c x).2; omega)]; exact hLP x hx)
      (fun t ht => by rw [gm₂]; exact wC t ht)
      ((F₂ 2550 (by omega) (by omega) (by omega)).trans r50)
      ((F₂ 2551 (by omega) (by omega) (by omega)).trans r51)
      ((F₂ 2552 (by omega) (by omega) (by omega)).trans r52)
      ((F₂ 2553 (by omega) (by omega) (by omega)).trans r53)
      ((F₂ 2554 (by omega) (by omega) (by omega)).trans r54)
      ((F₂ 2555 (by omega) (by omega) (by omega)).trans r55)
      ((F₂ 2556 (by omega) (by omega) (by omega)).trans r56)
      ((F₂ 2557 (by omega) (by omega) (by omega)).trans r57) g58 g59
      ((F₂ 2560 (by omega) (by omega) (by omega)).trans r60)
      ((F₂ 2561 (by omega) (by omega) (by omega)).trans r61)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) l2 l3 l4 hW
  refine ⟨c₃, t₁ + (t₂ + t₃), Exec.seq e₁ (Exec.seq e₂ e₃), by omega, i₀, hi₀,
    fun b hb => ?_, σ₀, νv₀, τ₀, a80, a93, a81, aRV, aNT, aNF, aIS, aLN, aG, fun a ha => ?_,
    fun r hr => by rw [af₃ r (by omega), F₂ r (by omega) (by omega) (by omega)], by rw [ar₃, grr₂, fr₁.rreg], by rw [arm₃, grm₂, fr₁.rmem], by rw [ao₃, go₂, fr₁.out]⟩
  · have hv := (vn (ψ b)).2
    rw [am₃ _ (Or.inl (by omega)), gm₂]
    exact wP b hb
  · rcases ha with h | h
    · rw [am₃ a (Or.inl (by omega)), M₂ a h]
    · rw [am₃ a (Or.inr h), gm₂, wm₁ a (Or.inr (by omega))]

end Side

end NegSSSP

end PlanarFlow
