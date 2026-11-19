module

public import PlanarFlow.NegSSSP.Enc.SdRun

/-!
# The plain arrays of the one-face instance of a side, on the machine

**`sdSide_exec`**: from the plain encoding of the piece map `kmap N K` (`Enc`, numbering `c` of
its `m` darts, as `faceWalk_side` reads it), the marks of a side `Z` (`sv` at `bz`), the flags of
`K` (`bK`), the lengths `(ℓ x).toNat` (`bL`) and the codes of the walk of `faceWalk_side` along
the boundary of `Z` from its start `i₀` (`bW`, `C.k` words), the program
`sdFull = (stA ; stV) ; sdProg` (the stellar subdivision `stPhase`, then `sdProg`) writes, within
`328 m + 13 (nV + nF) + 9 C.k + 52` steps (**linear**), the six plain arrays `RV NT NF IS LN G`
of the one-face instance `sideFD … i₀` of the side (the disc `discMap (kst N K) Z`, its face
`discFace hbd i₀`, its darts `side N K Z` embedded by `sideE hbd`, lengths `ℓ`) at
`I0, I0 + nD, …, I0 + 5 nD`, in the format of the hypotheses `hQRV … hQG` of
`fencNatNL_Dk_exec`, for some numberings `σ₀ νv₀ τ₀`; `nD = #DQ` in `r2580`, `#VQ` in `r2593`,
`#FQ − 1` in `r2581`. The memory outside `[bA, I0 + 5 nD + C.k)`, the registers outside
`[300, 314] ∪ [2562, 2593]`, the reals and the output are kept.

`sdSide_fd`: the same for the fields of `sideFD` (`fd.Q`, `fd.g`, `fd.P'`, `fd.e`, `fd.k`).
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

/-- **The program of the plain arrays of a side**: the stellar subdivision, then `sdProg`. -/
def sdFull : Stmt := .seq (.seq stA stV) sdProg

theorem sdSt_ok : (Stmt.seq stA stV).allI (sdOk 300 314) = true := by decide

theorem sdFull_natOnly : Klein.natOnly sdFull = true := by kernel_rfl

variable {P : Input} {W : ℕ}

section Side

variable {D : Type u} {V : Type v} {F : Type w} [Fintype D] [DecidableEq D] [Fintype V]
  [DecidableEq V] [Fintype F] [DecidableEq F] {N : CombMap D V F}
variable {K : Finset D} {C : (kst N K).SCycle} {Z : Finset (kst N K).Face}

set_option maxHeartbeats 4000000 in
/-- **The plain arrays of the one-face instance of a side, on the machine.** See the module
docstring. -/
theorem sdSide_exec (hrot : N.RotTrans) (hKr : K ⊆ reps N)
    (hbd : ∀ δ, ((kst N K).face δ ∈ Z ↔ (kst N K).face ((kst N K).α δ) ∈ Z) ↔ ¬ C.Mem δ)
    (i₀ : ℕ) (ℓ : D → ℤ) {m nV nF : ℕ} (c : SDart (rcl N K) ≃ Fin m)
    (vn : SVert (kσ N K) (rcl N K) ≃ Fin nV) (fn : (kmap N K).Face ≃ Fin nF)
    {bα bφ bφi bvn bfn bA bV bz sv bK bL bW S I0 : ℕ} (c₀ : Config) (hc : WordsBounded W c₀)
    (hE : Enc (kmap N K) c vn fn c₀.nmem bα bφ bφi bvn bfn)
    (hR : StR m bα bφ bφi bA bvn bfn bV nV c₀)
    (hz : ∀ x, ((kst N K).face (old x) ∈ Z ↔ c₀.nmem (bz + c x) = sv))
    (hKB : ∀ x, c₀.nmem (bK + c x) = if x.1 ∈ K then 1 else 0)
    (hLP : ∀ x : SDart (rcl N K), x.1 ∈ K → c₀.nmem (bL + c x) = (ℓ x.1).toNat)
    (hWk : ∀ t < C.k,
      c₀.nmem (bW + t) = (kmap N K).stCode c ((discCyc C Z).d ((i₀ + t) % C.k)))
    (r50 : c₀.nreg 2550 = m) (r51 : c₀.nreg 2551 = bz) (r52 : c₀.nreg 2552 = sv)
    (r53 : c₀.nreg 2553 = bA) (r54 : c₀.nreg 2554 = bV) (r55 : c₀.nreg 2555 = nV + nF)
    (r56 : c₀.nreg 2556 = bK) (r57 : c₀.nreg 2557 = bL) (r58 : c₀.nreg 2558 = bW)
    (r59 : c₀.nreg 2559 = C.k) (r60 : c₀.nreg 2560 = S) (r61 : c₀.nreg 2561 = I0)
    (l1 : bα + m ≤ bA) (l2 : bφ + m ≤ bA) (l3 : bφi + m ≤ bA) (l4 : bvn + m ≤ bA)
    (l5 : bfn + m ≤ bA) (l6 : bz + m ≤ bA) (l7 : bK + m ≤ bA) (l8 : bL + m ≤ bA)
    (l9 : bW + C.k ≤ bA) (l10 : bA + 3 * m ≤ bV) (l11 : bV + 3 * m ≤ S)
    (l12 : S + 7 * m + 2 * (nV + nF) ≤ I0) (hW : I0 + 18 * m + C.k + 5 ≤ W) :
    ∃ c' t, Exec P W sdFull c₀ c' t ∧ t ≤ 328 * m + 13 * (nV + nF) + 9 * C.k + 52 ∧
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
        (∀ a, a < bA ∨ I0 + 5 * Fintype.card (SDart (discDarts (kst N K) Z)) + C.k ≤ a →
          c'.nmem a = c₀.nmem a) ∧
        (∀ r, r < 300 ∨ (314 < r ∧ r < 2562) ∨ 2593 < r → c'.nreg r = c₀.nreg r) ∧
        c'.rreg = c₀.rreg ∧ c'.rmem = c₀.rmem ∧ c'.output = c₀.output := by
  set cd := (kmap N K).stCode c with hcd
  -- the stellar subdivision
  obtain ⟨c₁, t₁, e₁, ht₁, sA, -, sV, -, sm₁, -⟩ := stPhase (P := P) (kmap N K) c vn fn hE
    ⟨Or.inl l1, Or.inl l2, Or.inl l3, Or.inl l4, Or.inl l5, Or.inl (by omega), Or.inl (by omega),
      Or.inl (by omega), Or.inl l10⟩
    ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩ hc hR
  obtain ⟨K₁, kr₁, km₁, ko₁⟩ := sd_keep e₁ sdSt_ok
  have M₁ : ∀ a, a < bA → c₁.nmem a = c₀.nmem a := fun a h => sm₁ a (Or.inl h) (Or.inl (by omega))
  have R₁ : ∀ r, 2550 ≤ r → r ≤ 2561 → c₁.nreg r = c₀.nreg r := fun r h1 h2 =>
    K₁ r (Or.inr (by omega))
  have hcd3 : ∀ y < 3 * m, ∃ x, (cd x : ℕ) = y := fun y hy => ⟨cd.symm ⟨y, hy⟩, by simp⟩
  have hcm : ∀ x < m, ∃ d, (c d : ℕ) = x := fun x hx => ⟨c.symm ⟨x, hx⟩, by simp⟩
  -- the program
  obtain ⟨c₂, t₂, e₂, ht₂, o1, oG, o80, o81, o93, om₂, or₂, kr₂, km₂, ko₂⟩ :=
    sdProg_exec (P := P) c₁ e₁.wb_right (m := m) (bz := bz) (sv := sv) (bA := bA) (bV := bV)
      (nVF := nV + nF) (bK := bK) (bL := bL) (bW := bW) (kk := C.k) (S := S) (I0 := I0)
      ((R₁ 2550 (by omega) (by omega)).trans r50) ((R₁ 2551 (by omega) (by omega)).trans r51)
      ((R₁ 2552 (by omega) (by omega)).trans r52) ((R₁ 2553 (by omega) (by omega)).trans r53)
      ((R₁ 2554 (by omega) (by omega)).trans r54) ((R₁ 2555 (by omega) (by omega)).trans r55)
      ((R₁ 2556 (by omega) (by omega)).trans r56) ((R₁ 2557 (by omega) (by omega)).trans r57)
      ((R₁ 2558 (by omega) (by omega)).trans r58) ((R₁ 2559 (by omega) (by omega)).trans r59)
      ((R₁ 2560 (by omega) (by omega)).trans r60) ((R₁ 2561 (by omega) (by omega)).trans r61)
      (fun y hy => by obtain ⟨x, rfl⟩ := hcd3 y hy; rw [sA]; exact (cd _).2)
      (fun y hy => by obtain ⟨x, rfl⟩ := hcd3 y hy; rw [sV]; exact Fin.isLt _)
      (fun x hx => by
        obtain ⟨d, rfl⟩ := hcm x hx
        rw [M₁ _ (by omega), hKB]; split_ifs <;> omega)
      (fun t ht => by rw [M₁ _ (by omega), hWk t ht]; exact (cd _).2)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) l12 hW
  -- the arrays
  obtain ⟨σ₀, νv₀, τ₀, hcD, hcV, hcF, aRV, aNT, aNF, aIS, aLN, aG⟩ :=
    sd_arrays (C := C) (Z := Z) hrot hKr hbd i₀ ℓ c vn fn c₁.nmem c₂.nmem (bz := bz) (sv := sv)
      (bA := bA) (bV := bV) (bK := bK) (bL := bL) (bW := bW) (I0 := I0)
      (fun x => by rw [M₁ _ (by have := (c x).2; omega)]; exact hz x) sA sV
      (fun x => by rw [M₁ _ (by have := (c x).2; omega)]; exact hKB x)
      (fun x hx => by rw [M₁ _ (by have := (c x).2; omega)]; exact hLP x hx)
      (fun t ht => by rw [M₁ _ (by omega)]; exact hWk t ht)
      (fun y hy hf => (o1 y hy hf).1) (fun y hy hf => (o1 y hy hf).2.1)
      (fun y hy hf => (o1 y hy hf).2.2.1) (fun y hy hf => (o1 y hy hf).2.2.2.1)
      (fun y hy hf => (o1 y hy hf).2.2.2.2) oG
  refine ⟨c₂, t₁ + t₂, Exec.seq e₁ e₂, by omega, σ₀, νv₀, τ₀, by rw [o80, hcD],
    by rw [o93, hcV], by rw [o81, hcF], aRV, aNT, aNF, aIS, aLN, aG, fun a ha => ?_,
    fun r hr => ?_, by rw [kr₂, kr₁], by rw [km₂, km₁], by rw [ko₂, ko₁]⟩
  · rcases ha with h | h
    · rw [om₂ a (Or.inl (by omega)), M₁ a h]
    · rw [hcD] at h
      rw [om₂ a (Or.inr h), sm₁ a (Or.inr (by omega)) (Or.inr (by omega))]
  · rw [or₂ r (by omega), K₁ r (by omega)]

set_option maxHeartbeats 4000000 in
/-- **`sdSide_exec` for the fields of `sideFD`**: the hypotheses `hQRV … hQG` of
`fencNatNL_Dk_exec` for the one-face instance `fd = sideFD … i₀` of the side, at `I0` with
`nD = #fd.DQ`, written by `sdFull` within `328 m + 13 (nV + nF) + 9 fd.k + 52` steps. -/
theorem sdSide_fd (hM : N.IsPlane) (hrot : N.RotTrans) (hface : N.FaceTrans)
    (hKr : K ⊆ reps N) (hK0 : K.Nonempty) (hK : DConn N K) {ψ : V → SVert (kσ N K) (rcl N K)}
    (hψ : ∀ x : SDart (rcl N K), ψ (N.tail x.1) = (kmap N K).vert x)
    (hbd : ∀ δ, ((kst N K).face δ ∈ Z ↔ (kst N K).face ((kst N K).α δ) ∈ Z) ↔ ¬ C.Mem δ)
    {Bs : Finset V} (hBs : ∀ b ∈ Bs, b ∈ verts N (side N K Z) ∧ Sum.inl (ψ b) ∈ C.verts)
    {R : Finset D} (hR : Disjoint (verts N R) (verts N K)) {X : Finset D}
    (hX : X = side N K Z ∪ R) (i₀ : ℕ) (ℓ : D → ℤ) {m nV nF : ℕ} (c : SDart (rcl N K) ≃ Fin m)
    (vn : SVert (kσ N K) (rcl N K) ≃ Fin nV) (fn : (kmap N K).Face ≃ Fin nF)
    {bα bφ bφi bvn bfn bA bV bz sv bK bL bW S I0 : ℕ} (c₀ : Config) (hc : WordsBounded W c₀)
    (hE : Enc (kmap N K) c vn fn c₀.nmem bα bφ bφi bvn bfn)
    (hRg : StR m bα bφ bφi bA bvn bfn bV nV c₀)
    (hz : ∀ x, ((kst N K).face (old x) ∈ Z ↔ c₀.nmem (bz + c x) = sv))
    (hKB : ∀ x, c₀.nmem (bK + c x) = if x.1 ∈ K then 1 else 0)
    (hLP : ∀ x : SDart (rcl N K), x.1 ∈ K → c₀.nmem (bL + c x) = (ℓ x.1).toNat)
    (hWk : ∀ t < C.k,
      c₀.nmem (bW + t) = (kmap N K).stCode c ((discCyc C Z).d ((i₀ + t) % C.k)))
    (r50 : c₀.nreg 2550 = m) (r51 : c₀.nreg 2551 = bz) (r52 : c₀.nreg 2552 = sv)
    (r53 : c₀.nreg 2553 = bA) (r54 : c₀.nreg 2554 = bV) (r55 : c₀.nreg 2555 = nV + nF)
    (r56 : c₀.nreg 2556 = bK) (r57 : c₀.nreg 2557 = bL) (r58 : c₀.nreg 2558 = bW)
    (r59 : c₀.nreg 2559 = C.k) (r60 : c₀.nreg 2560 = S) (r61 : c₀.nreg 2561 = I0)
    (l1 : bα + m ≤ bA) (l2 : bφ + m ≤ bA) (l3 : bφi + m ≤ bA) (l4 : bvn + m ≤ bA)
    (l5 : bfn + m ≤ bA) (l6 : bz + m ≤ bA) (l7 : bK + m ≤ bA) (l8 : bL + m ≤ bA)
    (l9 : bW + C.k ≤ bA) (l10 : bA + 3 * m ≤ bV) (l11 : bV + 3 * m ≤ S)
    (l12 : S + 7 * m + 2 * (nV + nF) ≤ I0) (hW : I0 + 18 * m + C.k + 5 ≤ W) :
    let fd := sideFD hM hrot hface hKr hK0 hK hψ hbd hBs hR hX i₀
    ∃ c' t, Exec P W sdFull c₀ c' t ∧ t ≤ 328 * m + 13 * (nV + nF) + 9 * fd.k + 52 ∧
      ∃ (σ₀ : fd.DQ ≃ Fin (Fintype.card fd.DQ)) (νv₀ : fd.VQ ≃ Fin (Fintype.card fd.VQ))
        (τ₀ : fd.FQ ≃ Fin (Fintype.card fd.FQ)),
        c'.nreg 2580 = Fintype.card fd.DQ ∧ c'.nreg 2593 = Fintype.card fd.VQ ∧
        c'.nreg 2581 + 1 = Fintype.card fd.FQ ∧
        (∀ d, c'.nmem (I0 + σ₀ d) = σ₀ (fd.Q.rev d)) ∧
        (∀ d, c'.nmem (I0 + Fintype.card fd.DQ + σ₀ d) = νv₀ (fd.Q.tail d)) ∧
        (∀ d, c'.nmem (I0 + 2 * Fintype.card fd.DQ + σ₀ d) = τ₀ (fd.Q.face d)) ∧
        (∀ d, c'.nmem (I0 + 3 * Fintype.card fd.DQ + σ₀ d) =
          if d ∈ fd.P'.image fd.e then 1 else 0) ∧
        (∀ d, c'.nmem (I0 + 4 * Fintype.card fd.DQ + σ₀ d) = (faceLen fd.P' fd.e ℓ d).toNat) ∧
        (∀ i < fd.k, c'.nmem (I0 + 5 * Fintype.card fd.DQ + i) = σ₀ (fd.g i)) ∧
        (∀ a, a < bA ∨ I0 + 5 * Fintype.card fd.DQ + fd.k ≤ a → c'.nmem a = c₀.nmem a) ∧
        (∀ r, r < 300 ∨ (314 < r ∧ r < 2562) ∨ 2593 < r → c'.nreg r = c₀.nreg r) ∧
        c'.rreg = c₀.rreg ∧ c'.rmem = c₀.rmem ∧ c'.output = c₀.output :=
  sdSide_exec hrot hKr hbd i₀ ℓ c vn fn c₀ hc hE hRg hz hKB hLP hWk r50 r51 r52 r53 r54 r55 r56
    r57 r58 r59 r60 r61 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 hW

end Side

end NegSSSP

end PlanarFlow
