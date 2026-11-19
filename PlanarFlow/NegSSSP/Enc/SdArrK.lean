module

public import PlanarFlow.NegSSSP.Enc.SideArr

/-!
# The side arrays exporting the length of the face

`sdWalk_exec_k`, `sdArr_exec_k`: `sdWalk_exec'`, `sdArr_exec` (same programs, same bounds) with,
in addition, `r2559 = C.k` at the end (the length of the face of the side's instance, a size
the node's parameter program needs: `p.k = fd.k`). The proofs are those of `sdWalk_exec'` and
`sdArr_exec` (`sdWSet` sets `r2559 := r829 = C.k`, `sdSide` keeps it).
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
theorem sdWalk_exec_k (hrot : N.RotTrans) (hKr : K ⊆ reps N) {ψ : V → SVert (kσ N K) (rcl N K)}
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
        c'.nreg 2559 = C.k ∧
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
    fun b hb => ?_, σ₀, νv₀, τ₀, a80, a93, a81, aRV, aNT, aNF, aIS, aLN, aG, by rw [af₃ 2559 (by omega)]; exact g59, fun a ha => ?_,
    fun r hr => by rw [af₃ r (by omega), F₂ r (by omega) (by omega) (by omega)], by rw [ar₃, grr₂, fr₁.rreg], by rw [arm₃, grm₂, fr₁.rmem], by rw [ao₃, go₂, fr₁.out]⟩
  · have hv := (vn (ψ b)).2
    rw [am₃ _ (Or.inl (by omega)), gm₂]
    exact wP b hb
  · rcases ha with h | h
    · rw [am₃ a (Or.inl (by omega)), M₂ a h]
    · rw [am₃ a (Or.inr h), gm₂, wm₁ a (Or.inr (by omega))]

set_option maxHeartbeats 4000000 in
/-- **The plain arrays of a side, as one run** (see the module docstring). -/
theorem sdArr_exec_k (hrot : N.RotTrans) (hKr : K ⊆ reps N) {ψ : V → SVert (kσ N K) (rcl N K)}
    (hbd : ∀ δ, ((kst N K).face δ ∈ Z ↔ (kst N K).face ((kst N K).α δ) ∈ Z) ↔ ¬ C.Mem δ)
    {Bs : Finset V} (hBs : ∀ b ∈ Bs, Sum.inl (ψ b) ∈ C.verts)
    {Pc : Finset D} {m k : ℕ} {en : ℕ → D} {α σ : ℕ → ℕ} (he : PEnc N Pc m k en α σ)
    (hKP : K ⊆ Pc) (ℓ : D → ℤ) (pot : V → ℤ)
    {m' nV nF : ℕ} (cn : SDart (rcl N K) ≃ Fin m') (vn : SVert (kσ N K) (rcl N K) ≃ Fin nV)
    (fn : (kmap N K).Face ≃ Fin nF)
    {Y bz sv bK bL Xb Fb Lb Tb Hb Db M Ob T₀ Ck I0 : ℕ}
    (c₀ : Config) (hw : WordsBounded W c₀)
    (hE : Enc (kmap N K) cn vn fn c₀.nmem Y (Y + m') (Y + 2 * m') (Y + 3 * m') (Y + 4 * m'))
    (hz : ∀ x, ((kst N K).face (old x) ∈ Z ↔ c₀.nmem (bz + cn x) = sv))
    (hKB : ∀ x, c₀.nmem (bK + cn x) = if x.1 ∈ K then 1 else 0)
    (hXm : ∀ h < k, ∀ hm : en h ∈ rcl N K, c₀.nmem (Xb + h) = cn ⟨en h, hm⟩)
    (hFm : ∀ x < m, (c₀.nmem (Fb + x) ≠ 0 ↔ en x ∈ K))
    (hl : ∀ i < m, (c₀.nmem (Lb + i) : ℤ) = ℓ (en i) % M)
    (ht : ∀ i < m, (c₀.nmem (Db + c₀.nmem (Tb + i)) : ℤ) = pot (N.tail (en i)) % M)
    (hh : ∀ i < m, (c₀.nmem (Db + c₀.nmem (Hb + i)) : ℤ) = pot (N.head (en i)) % M)
    (hred : ∀ d ∈ side N K Z, 0 ≤ redLen N ℓ pot d ∧ redLen N ℓ pot d < M)
    (hCk : C.k ≤ Ck) (hM : 0 < M)
    -- the registers
    (r50 : c₀.nreg 2750 = m) (r51 : c₀.nreg 2751 = Lb) (r52 : c₀.nreg 2752 = Tb)
    (r53 : c₀.nreg 2753 = Hb) (r54 : c₀.nreg 2754 = Db) (r55 : c₀.nreg 2755 = M)
    (r56 : c₀.nreg 2756 = Ob)
    (r76 : c₀.nreg 2776 = m') (r77 : c₀.nreg 2777 = bL) (r78 : c₀.nreg 2778 = m)
    (r79 : c₀.nreg 2779 = Fb) (r80 : c₀.nreg 2780 = Xb) (r81 : c₀.nreg 2781 = Ob)
    (r960 : c₀.nreg 960 = m') (r961 : c₀.nreg 961 = nV) (r962 : c₀.nreg 962 = nF)
    (r801 : c₀.nreg 801 = Y) (r90 : c₀.nreg 2790 = T₀) (r91 : c₀.nreg 2791 = bz)
    (r92 : c₀.nreg 2792 = sv) (r93 : c₀.nreg 2793 = bK) (r94 : c₀.nreg 2794 = bL)
    (r95 : c₀.nreg 2795 = Ck) (r96 : c₀.nreg 2796 = I0)
    -- the layout: the split's data below `Ob`, then `RL`, `bL`, the walk's area
    (hlo : Y + 5 * m' ≤ Ob ∧ bz + m' ≤ Ob ∧ bK + m' ≤ Ob ∧ Xb + k ≤ Ob ∧ Fb + m ≤ Ob)
    (hOb : Ob + m ≤ bL) (hbL : bL + m' ≤ T₀) (hmk : m ≤ k)
    (dL : Ob + m ≤ Lb ∨ Lb + m ≤ Ob) (dT : Ob + m ≤ Tb ∨ Tb + m ≤ Ob)
    (dH : Ob + m ≤ Hb ∨ Hb + m ≤ Ob)
    (hT : ∀ i < m, Db + c₀.nmem (Tb + i) ≤ W ∧
      (Db + c₀.nmem (Tb + i) < Ob ∨ Ob + m ≤ Db + c₀.nmem (Tb + i)))
    (hH : ∀ i < m, Db + c₀.nmem (Hb + i) ≤ W ∧
      (Db + c₀.nmem (Hb + i) < Ob ∨ Ob + m ≤ Db + c₀.nmem (Hb + i)))
    (wL : Lb + m ≤ W) (wT : Tb + m ≤ W) (wH : Hb + m ≤ W) (hMW : 3 * M ≤ W)
    (l4 : swA T₀ m' nV nF Ck + 13 * m' + 2 * (nV + nF) ≤ I0)
    (hW : I0 + 18 * m' + C.k + 5 ≤ W) (h6 : 6 ≤ W) :
    ∃ c' t, Exec P W sdArr c₀ c' t ∧
      t ≤ 33 * m + 405 * m' + 13 * (nV + nF) + 22 * C.k + 130 ∧ ∃ i₀ < C.k,
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
          (faceLen (side N K Z) (sideE hbd) (redLen N ℓ pot) d).toNat) ∧
        (∀ i < C.k, c'.nmem (I0 + 5 * Fintype.card (SDart (discDarts (kst N K) Z)) + i) =
          σ₀ (discFace hbd i₀ i)) ∧
        c'.nreg 2559 = C.k ∧
        (∀ a, (a < Ob ∨ (Ob + m ≤ a ∧ a < bL) ∨ (bL + m' ≤ a ∧ a < T₀) ∨
          I0 + 5 * Fintype.card (SDart (discDarts (kst N K) Z)) + C.k ≤ a) →
          c'.nmem a = c₀.nmem a) ∧
        (∀ r, r ≠ 10 → (r < 300 ∨ 318 < r) → (r < 800 ∨ 840 < r) → (r < 2550 ∨ 2593 < r) →
          (r < 2750 ∨ 2798 < r) → c'.nreg r = c₀.nreg r) ∧
        c'.rreg = c₀.rreg ∧ c'.rmem = c₀.rmem ∧ c'.output = c₀.output := by
  obtain ⟨l1, l2, l3, l4', l5⟩ := hlo
  have hsw : T₀ ≤ swA T₀ m' nV nF Ck := by unfold swA; omega
  have hres : ∀ i < m, c₀.nmem (Lb + i) < M ∧ c₀.nmem (Db + c₀.nmem (Tb + i)) < M :=
    fun i hi => by
      have a := Int.emod_lt_of_pos (ℓ (en i)) (by exact_mod_cast hM : (0 : ℤ) < M)
      have b := Int.emod_lt_of_pos (pot (N.tail (en i))) (by exact_mod_cast hM : (0 : ℤ) < M)
      have := hl i hi; have := ht i hi
      omega
  -- the reduced lengths
  obtain ⟨c₁, t₁, e₁, ht₁, o₁, m₁, f₁, rr₁, rm₁, oo₁⟩ := rlProg_exec' (P := P) c₀ hw r50 r51 r52
    r53 r54 r55 r56 hM hMW (by omega) wL wT wH (by omega) dL dT dH hT hH hres
  have M₁ : ∀ a, a < Ob → c₁.nmem a = c₀.nmem a := fun a h => m₁ a (Or.inl h)
  have F₁ : ∀ r, (r < 2750 ∨ 2763 < r) → c₁.nreg r = c₀.nreg r := f₁
  -- the scatter
  have hmk := he.mle
  have hXm₁ : ∀ h < k, ∀ hm : en h ∈ rcl N K, c₁.nmem (Xb + h) = cn ⟨en h, hm⟩ :=
    fun h hk hm => by rw [M₁ _ (by omega)]; exact hXm h hk hm
  have hFm₁ : ∀ x < m, (c₁.nmem (Fb + x) ≠ 0 ↔ en x ∈ K) := fun x hx => by
    rw [M₁ _ (by omega)]; exact hFm x hx
  obtain ⟨c₂, t₂, e₂, ht₂, o₂, m₂, f₂, rr₂, rm₂, oo₂⟩ := blProg_exec (P := P) (m' := m') (m := m)
    (Kb := bL) (Fb := Fb) (Xb := Xb) (Rb := Ob) c₁ e₁.wb_right
    ((F₁ 2776 (by omega)).trans r76) ((F₁ 2777 (by omega)).trans r77)
    ((F₁ 2778 (by omega)).trans r78) ((F₁ 2779 (by omega)).trans r79)
    ((F₁ 2780 (by omega)).trans r80) ((F₁ 2781 (by omega)).trans r81) (by omega) (by omega)
    (by omega) (by omega) (by omega) (Or.inr (by omega)) (Or.inr (by omega)) (Or.inr hOb)
    (bk_idx he cn hXm₁ hFm₁)
  have M₂ : ∀ a, a < Ob → c₂.nmem a = c₀.nmem a := fun a h => by
    rw [m₂ a (Or.inl (by omega))]; exact M₁ a h
  have F₂ : ∀ r, (r < 2750 ∨ 2788 < r) → c₂.nreg r = c₀.nreg r := fun r h => by
    rw [f₂ r (by omega)]; exact F₁ r (by omega)
  have hLP : ∀ x : SDart (rcl N K), x.1 ∈ K →
      c₂.nmem (bL + cn x) = (blLen c₁.nmem Ob m en x.1).toNat := fun x hx => by
    rw [o₂ _ (cn x).2]; exact bl_hLP he hKP cn hXm₁ hFm₁ x hx
  -- the registers of the walk
  obtain ⟨c₃, t₃, e₃, ht₃, g10, g800, g801, g802, g803, g804, g805, g806, g807, g808, g809, g810,
      gR, g50, g51, g52, g53, g54, g55, g56, g57, g60, g61, gf, gm, gr, grm, go⟩ :=
    swSet_exec (P := P) (m := m') (nV := nV) (nF := nF) (Y := Y) (T₀ := T₀) (bz := bz) (sv := sv)
      (bK := bK) (bL := bL) (Ck := Ck) (I0 := I0) c₂ e₂.wb_right
      ((F₂ 960 (by omega)).trans r960) ((F₂ 961 (by omega)).trans r961)
      ((F₂ 962 (by omega)).trans r962) ((F₂ 801 (by omega)).trans r801)
      ((F₂ 2790 (by omega)).trans r90) ((F₂ 2791 (by omega)).trans r91)
      ((F₂ 2792 (by omega)).trans r92) ((F₂ 2793 (by omega)).trans r93)
      ((F₂ 2794 (by omega)).trans r94) ((F₂ 2795 (by omega)).trans r95)
      ((F₂ 2796 (by omega)).trans r96) (by omega) (by omega) h6
  have M₃ : ∀ a, a < Ob → c₃.nmem a = c₀.nmem a := fun a h => by rw [gm]; exact M₂ a h
  have hE₃ : Enc (kmap N K) cn vn fn c₃.nmem Y (Y + m') (Y + 2 * m') (Y + 3 * m')
      (Y + 4 * m') := enc_congr hE fun i hi =>
    ⟨M₃ _ (by omega), M₃ _ (by omega), M₃ _ (by omega), M₃ _ (by omega), M₃ _ (by omega)⟩
  -- the walk
  obtain ⟨c₄, t₄, e₄, ht₄, i₀, hi₀, hpos, σ₀, νv₀, τ₀, a80, a93, a81, aRV, aNT, aNF, aIS, aLN,
      aG, a59, am, af, ar, arm, ao⟩ :=
    sdWalk_exec_k (P := P) (W := W) (C := C) (Z := Z) hrot hKr hbd hBs
      (blLen c₁.nmem Ob m en) cn vn fn (bα := Y) (bφ := Y + m') (bφi := Y + 2 * m')
      (bvn := Y + 3 * m') (bfn := Y + 4 * m') (bz := bz) (sv := sv) (T₀ := T₀)
      (bA := swA T₀ m' nV nF Ck) (bV := swA T₀ m' nV nF Ck + 3 * m') (bK := bK) (bL := bL)
      (S := swA T₀ m' nV nF Ck + 6 * m') (I0 := I0) c₃ e₃.wb_right hE₃
      (fun x => by rw [M₃ _ (by have := (cn x).2; omega)]; exact hz x)
      (fun x => by rw [M₃ _ (by have := (cn x).2; omega)]; exact hKB x)
      (fun x hx => by rw [gm]; exact hLP x hx)
      ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
      g10 g800 g801 g802 g803 g804 g805 g806 g807 g808 g809 g810 gR g50 g51 g52 g53 g54 g55 g56
      g57 g60 g61 (by unfold swA; omega) (by omega) (by omega) (by omega) hW
  have hfl : faceLen (side N K Z) (sideE hbd) (blLen c₁.nmem Ob m en) =
      faceLen (side N K Z) (sideE hbd) (redLen N ℓ pot) :=
    faceLen_congr fun d hd => blLen_red he.enumP hM o₁ ℓ pot hl ht hh
      (hKP (side_subset Z hd)) (hred d hd).1 (hred d hd).2
  rw [hfl] at aLN
  refine ⟨c₄, t₁ + (t₂ + (t₃ + t₄)), .seq e₁ (.seq e₂ (.seq e₃ e₄)), by omega, i₀, hi₀, hpos,
    σ₀, νv₀, τ₀, a80, a93, a81, aRV, aNT, aNF, aIS, aLN, aG, a59, fun a ha => ?_,
    fun r h1 h2 h3 h4 h5 => ?_, by rw [ar, gr, rr₂, rr₁], by rw [arm, grm, rm₂, rm₁],
    by rw [ao, go, oo₂, oo₁]⟩
  · rw [am a (by omega), gm, m₂ a (by omega), m₁ a (by omega)]
  · rw [af r (by omega), gf r h1 h2 (by omega) (by omega) (by omega) (by omega),
      f₂ r (by omega), F₁ r (by omega)]

end Side

end NegSSSP

end PlanarFlow
