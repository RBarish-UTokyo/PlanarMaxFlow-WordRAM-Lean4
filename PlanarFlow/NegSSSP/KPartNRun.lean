module

public import PlanarFlow.NegSSSP.KPartN

/-!
# One part of a node on natural words: the run

`kpartN_exec`: for a one-face instance `fd` of the part `X` of a node and an encoding meeting
`FEncNat` (the isolating lengths of the reduced lengths, `Hc ≥ kleinHI`), from every natural
configuration holding the inputs in the layout `KLayN`, with the encoding in a natural slot
(`KSlotN`: the input words at `β`, the residues modulo `2 Hc + 1` of Klein's real constants at
`RkN`) and the residues modulo `M` of the potentials at `βN + δb`, the natural program
`kPartN` runs to the order `β'` of the boundary (vertex numbers at `Ys + S`) and the matrices of
`bfStartP` for `childDDG N mssp X ℓ δ B` in this order: the flags at `Ys + 3 S` and **the
residues modulo `M` of the lengths at `βN + Ys + 3 S`** (`KPartRunN`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace NegSSSP

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs BKMNW Monge

/-- **The natural slot of an encoding**: the input words at `β + i` (`i ≤ Kw`), and the residues
modulo `Mo` of Klein's real constants at `RkN + a` (`a < 3 nD + 3`). -/
structure KSlotN {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
    [Fintype F] [DecidableEq F] (M : CombMap D V F) (k : ℕ) (g : ℕ → D) (S : Finset D)
    (ℓ : D → ℤ) {nD : ℕ} (σ : D ≃ Fin nD) (B n β RkN Mo : ℕ) (P : Input) (d : Config) : Prop where
  dat : ∀ i ≤ B + 16 * (n + 1), d.nmem (β + i) = P.data.getD i 0
  res : ∀ a < 3 * nD + 3, d.nmem (RkN + a) = Klein.resW Mo (Klein.kConst V M k g S ℓ σ a : ℝ)

/-- **The layout of `kPartN`**: the five regions `Ys + i S` (`i < 5`) above the work space of
Klein's program and the copy of its input words (`[0, 2 Kw + 1]`); the inputs (the list `Lb`,
the positions `Pb`, the potentials `δb` by vertex number, the input words at `β`, the residues
of the constants at `RkN`) above it and apart from the regions; all below `W'`; the node's real
image at `βN > W'` and Klein's real image at `βK > βN + W'`. -/
structure KLayN (b w k nD n Kw Lb Pb δb Ys S β RkN βK βN W' : ℕ) : Prop where
  sk : k ≤ S
  sb : b ≤ S
  sbb : b * b ≤ S
  kY : 2 * Kw + 1 < Ys
  rbY : n + k * k ≤ Ys
  yW : Ys + 5 * S ≤ W'
  lK : 2 * Kw + 1 < Lb
  lY : Lb + b ≤ Ys ∨ Ys + 5 * S ≤ Lb
  lW : Lb + b ≤ W'
  pK : 2 * Kw + 1 < Pb
  pY : Pb + w ≤ Ys ∨ Ys + 5 * S ≤ Pb
  pW : Pb + w ≤ W'
  dY : δb + w ≤ Ys ∨ Ys + 5 * S ≤ δb
  dW : δb + w ≤ W'
  bK : 2 * Kw + 1 < β
  bY : β + Kw < Ys ∨ Ys + 5 * S ≤ β
  bW : β + Kw ≤ W'
  rK : 2 * Kw + 1 < RkN
  rY : RkN + (3 * nD + 3) ≤ Ys ∨ Ys + 5 * S ≤ RkN
  rW : RkN + (3 * nD + 3) ≤ W'
  nW : W' < βN
  kN : βN + W' < βK
  wW : w + 1 ≤ W'
  bbW : b * b + 1 ≤ W'

/-- The cost bound of `kPartN`. -/
def partNCost (m k b Kw nD : ℕ) : ℕ :=
  12 * (32886 * 2372500000 * m * lg m) + 14 * (k * k) + 19 * k + 10 * b + 17 * Kw + 21 * nD +
    36 * (b * b) + 937

universe u v w

variable {D : Type u} {V : Type v} {F : Type w} [Fintype D] [DecidableEq D] [Fintype V]
  [DecidableEq V] {N : CombMap D V F}

/-- **The run of one part on natural words** (the conclusion of `kpartN_exec`). -/
def KPartRunN (N : CombMap D V F) (P P₀ P₁ X : Finset D) (ℓ : D → ℤ) (δ : V → ℤ)
    (mssp : Finset D → (D → ℤ) → Finset V → V → V → Option ℤ)
    (fd : FaceData N X (bdry N P₀ P₁)) (n Bw : ℕ)
    (σ : Klein.SrcD fd.DQ fd.k ≃ Fin (Fintype.card (Klein.SrcD fd.DQ fd.k)))
    (wt : Klein.SrcD fd.DQ fd.k → ℤ) (Pk : Input) (Hc : ℕ) : Prop :=
  ∀ {m w b : ℕ} {e : ℕ → D} {ν : V → ℕ} {ι : ℕ → V}, NodeEnc N P₀ P₁ m w e ν ι →
  ∀ {src : ℕ → V}, IsEnum b src (bdry N P₀ P₁) →
  ∀ (Lb Pb δb Ys S β RkN βK βN M W' WN : ℕ) (I : Input) (d : Config),
    KLayN b w fd.k (Fintype.card (Klein.SrcD fd.DQ fd.k)) n (Bw + 16 * (n + 1)) Lb Pb δb Ys S
      β RkN βK βN W' →
    βK + (2 * (Bw + 16 * (n + 1)) + 1) + (2 * Hc + 1) * (2 * Hc + 1) + (2 * Hc + 1) ≤ WN →
    0 < M → 2 * Hc + 1 + 2 * M ≤ WN →
    Klein.srcN1 fd.VQ fd.FQ fd.DQ fd.k ≤ WN →
    (Klein.srcW (fd.P'.image fd.e) (faceLen fd.P' fd.e (redLen N ℓ δ))).toNat ≤ WN →
    WordsBounded WN d →
    d.nreg 802 = b → d.nreg 960 = Lb → d.nreg 961 = Ys → d.nreg 962 = Ys + S →
    d.nreg 963 = Ys + 2 * S → d.nreg 964 = Ys + 3 * S → d.nreg 965 = Ys + 4 * S →
    d.nreg 966 = δb →
    (∀ i < b, d.nmem (Lb + i) = ν (src i)) →
    (∀ x ∈ bdry N P₀ P₁, d.nmem (Pb + ν x) < fd.k ∧
      fd.Q.tail (fd.g (d.nmem (Pb + ν x))) = fd.j x) →
    (∀ v < w, ModNat.Res M (δ (ι v) : ℝ) (d.nmem (βN + δb + v))) →
    KSlotN (Klein.srcMap fd.inst.cycle) fd.k (Klein.srcG fd.inst.cycle)
      (Klein.srcPiece fd.k (fd.P'.image fd.e))
      (Klein.srcIso (V := fd.VQ) (F := fd.FQ) fd.k (fd.P'.image fd.e)
        (faceLen fd.P' fd.e (redLen N ℓ δ)) wt σ) σ Bw n β RkN (2 * Hc + 1) Pk d →
    (∀ a ≤ Bw + 16 * (n + 1), d.nmem a ≤ Bw + 16 * (n + 1)) →
    (∀ r < 752, d.nreg r ≤ W') → (∀ a ≤ W', d.nmem a ≤ W') →
    ∃ d' t, ∃ β' : ℕ → V,
      Exec I WN (kPartN ⟨fd.k, Fintype.card (Klein.SrcD fd.DQ fd.k), n, Bw, Pk.data.length, β,
        RkN, Pb, Hc, Klein.srcN1 fd.VQ fd.FQ fd.DQ fd.k,
        (Klein.srcW (fd.P'.image fd.e) (faceLen fd.P' fd.e (redLen N ℓ δ))).toNat, βK, βN, M⟩)
        d d' t ∧
      t ≤ partNCost P.card fd.k b (Bw + 16 * (n + 1)) (Fintype.card (Klein.SrcD fd.DQ fd.k)) ∧
      IsEnum b β' (bdry N P₀ P₁) ∧ (∀ x < b, d'.nmem (Ys + S + x) = ν (β' x)) ∧
      Monge.CrossingO b (fun i i' => (childDDG N mssp X ℓ δ (bdry N P₀ P₁)).len (β' i)
        (β' i')) ∧
      (∀ s < b, ∀ t < b,
        d'.nmem (Ys + 3 * S + (s * b + t)) =
            finB (arcOf (childDDG N mssp X ℓ δ (bdry N P₀ P₁)) β') s t ∧
          ModNat.Res M (matOf (childDDG N mssp X ℓ δ (bdry N P₀ P₁)) β' s t : ℝ)
            (d'.nmem (βN + (Ys + 3 * S + (s * b + t))))) ∧
      (∀ r, (752 ≤ r ∧ r < 910) ∨ 919 ≤ r → d'.nreg r = d.nreg r) ∧
      (∀ a, 2 * (Bw + 16 * (n + 1)) + 1 < a → (a < Ys ∨ Ys + 5 * S ≤ a) →
        (a < βN + (Ys + 3 * S) ∨ βN + (Ys + 3 * S) + b * b ≤ a) →
        (a < βK ∨ βK + (2 * (Bw + 16 * (n + 1)) + 1) < a) → d'.nmem a = d.nmem a) ∧
      d'.rreg = d.rreg ∧ d'.rmem = d.rmem ∧
      (∀ a ≤ 2 * (Bw + 16 * (n + 1)) + 1, d'.nmem a ≤ Bw + 16 * (n + 1)) ∧
      d'.output = d.output ∧
      (∀ r, r < 408 ∨ (910 ≤ r ∧ r < 919) → d'.nreg r = 0) ∧ (∀ r < 752, d'.nreg r ≤ W') ∧
      (∀ a ≤ W', d'.nmem a ≤ W')

set_option maxHeartbeats 8000000 in
/-- **One part of a node on natural words** (see the module docstring). -/
theorem kpartN_exec {P P₀ P₁ X : Finset D} {ℓ : D → ℤ} {δ : V → ℤ}
    (hnn : ∀ d ∈ X, 0 ≤ redLen N ℓ δ d)
    {mssp : Finset D → (D → ℤ) → Finset V → V → V → Option ℤ} (hmssp : PieceMSSPSpec N mssp)
    (fd : FaceData N X (bdry N P₀ P₁)) (hq : fd.q ≤ 18 * P.card) (hk : fd.k ^ 2 ≤ 1200 * P.card)
    {n Bw : ℕ} {σ : Klein.SrcD fd.DQ fd.k ≃ Fin (Fintype.card (Klein.SrcD fd.DQ fd.k))}
    {wt : Klein.SrcD fd.DQ fd.k → ℤ} {Pk : Input} (hv : FEncNat fd (redLen N ℓ δ) n Bw σ wt Pk)
    {Hc : ℕ} (hHc : fdHI fd (redLen N ℓ δ) σ wt ≤ Hc) :
    KPartRunN N P P₀ P₁ X ℓ δ mssp fd n Bw σ wt Pk Hc := by
  classical
  unfold KPartRunN
  intro m w b e ν ι hN src hsrc Lb Pb δb Ys S β RkN βK βN M W' WN I d hL hWK hM0 hWM hN1 hWc hd
    r802 r960 r961 r962 r963 r964 r965 r966 hsl hpos hδ hK hlow hRW hMW
  set Kw := Bw + 16 * (n + 1) with hKw
  set Mo := 2 * Hc + 1 with hMo
  set Wc := (Klein.srcW (fd.P'.image fd.e) (faceLen fd.P' fd.e (redLen N ℓ δ))).toNat with hWcd
  set N1 := Klein.srcN1 fd.VQ fd.FQ fd.DQ fd.k with hN1d
  obtain ⟨sk, sb, sbb, kY, rbY, yW, lK, lY, lW, pK, pY, pW, dY, dW, bK, bY, bW, rK, rY, rW, nW,
    kN, wW, bbW⟩ := hL
  have hv₀ := hv
  obtain ⟨-, -, -, hKV⟩ := hv
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hWa, hB, hOUT, hRB, hP, -⟩ := hKV
  have hk2 : fd.k * fd.k ≤ Bw := by unfold Klein.aOUT at hOUT; nlinarith
  have hnD3 : 3 * Fintype.card (Klein.SrcD fd.DQ fd.k) + 3 ≤ Bw := by unfold Klein.aOUT at hOUT; omega
  have hn' : n ≤ Bw := by omega
  have hνlt : ∀ i < b, ν (src i) < w := fun i hi => hN.lt _ (bdry_sub_verts (hsrc.mem i hi))
  have hWN : W' < WN := by omega
  -- 1. the registers of `cornerProg`
  obtain ⟨c₁, t₁, e₁, ht₁, g10, g740, g741, g742, g743, g744, g745, g746, gn₁, grr₁, gnm₁, grm₁,
    go₁⟩ := kpC_exec (I := I) (k := fd.k) (Pb := Pb) (W := WN) (by pomega) (by pomega) d hd
      (by pomega)
  -- 2. the corners, run on the truncation at the word bound `W'` and lifted
  have hcU : cornerProg.regsOK (fun r => decide (r < 752)) = true := by decide +kernel
  have hcI : cornerProg.noInp = true := by decide +kernel
  have hcR : cornerProg.noRand = true := by decide +kernel
  have hRW₁ : ∀ r < 752, c₁.nreg r ≤ W' := fun r hr => by
    by_cases h10 : r = 10
    · subst h10; rw [g10]; pomega
    by_cases h74 : 740 ≤ r ∧ r ≤ 746
    · rcases (by omega : r = 740 ∨ r = 741 ∨ r = 742 ∨ r = 743 ∨ r = 744 ∨ r = 745 ∨ r = 746)
        with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · rw [g740]; pomega
      · rw [g741, r802]; pomega
      · rw [g742, r960]; pomega
      · rw [g743]; pomega
      · rw [g744, r961]; pomega
      · rw [g745, r962]; pomega
      · rw [g746, r963]; pomega
    · rw [gn₁ r h10 (by omega)]; exact hRW r hr
  have hwt : WordsBounded W' (trunc (fun r => decide (r < 752)) W' c₁) :=
    wordsBounded_trunc (fun r hr => hRW₁ r (by simpa using hr))
      (fun a ha => by rw [gnm₁]; exact hMW a ha)
  have hA₁ := agree_trunc (fun r => decide (r < 752)) W' c₁
  have hCL : CornerLay fd.k b w Lb Pb Ys (Ys + S) (Ys + 2 * S) W' (fun i => ν (src i)) :=
    ⟨hνlt, by pomega, by pomega, by pomega, by pomega, by pomega, by pomega, by pomega,
      by pomega, by pomega, by pomega, by pomega, by pomega, by pomega⟩
  have hCI : CornerIn fd.k b Lb Pb Ys (Ys + S) (Ys + 2 * S) (fun i => ν (src i))
      (trunc (fun r => decide (r < 752)) W' c₁) :=
    ⟨by rw [← hA₁.nreg 10 (by decide)]; exact g10,
      by rw [← hA₁.nreg 740 (by decide)]; exact g740,
      by rw [← hA₁.nreg 741 (by decide), g741, r802],
      by rw [← hA₁.nreg 742 (by decide), g742, r960],
      by rw [← hA₁.nreg 743 (by decide)]; exact g743,
      by rw [← hA₁.nreg 744 (by decide), g744, r961],
      by rw [← hA₁.nreg 745 (by decide), g745, r962],
      by rw [← hA₁.nreg 746 (by decide), g746, r963],
      fun i hi => by rw [← hA₁.nmem _ (by pomega), gnm₁]; exact hsl i hi⟩
  obtain ⟨c₂s, t₂, β', e₂s, ht₂, -, hen, hO₂s, hS₂s, hcr, hfr₂s, hcf₂⟩ :=
    cornerProg_crossingO (P := I) fd.inst hsrc hCL _ hwt hCI
      (fun i hi => by
        have := hνlt i hi
        rw [← hA₁.nmem _ (by pomega), gnm₁]; exact hpos _ (hsrc.mem i hi))
  obtain ⟨c₂, e₂, hA₂, hK₂, ho₂⟩ := Exec.lift_trunc (P' := I) e₂s hcU hcI hcR (W' := WN)
    (by pomega) e₁.wb_right
  have hO₂ : ∀ x < b, c₂.nmem (Ys + S + x) = ν (β' x) := fun x hx => by
    rw [hA₂.nmem _ (by pomega)]; exact hO₂s x hx
  have hS₂ : ∀ x < b, c₂.nmem (Ys + 2 * S + x) < fd.k ∧
      fd.j (β' x) = fd.Q.tail (fd.g (c₂.nmem (Ys + 2 * S + x))) := fun x hx => by
    rw [hA₂.nmem _ (by pomega)]; exact hS₂s x hx
  have hm₂ : ∀ a, (a < Ys ∨ Ys + 3 * S ≤ a) → c₂.nmem a = d.nmem a := fun a ha => by
    by_cases haW : a ≤ W'
    · rw [hA₂.nmem a haW, hfr₂s a (by pomega) (by pomega) (by pomega), ← hA₁.nmem a haW, gnm₁]
    · rw [hK₂.nmem a (by omega), gnm₁]
  have hR₂ : ∀ r, (752 ≤ r ∧ r < 910) ∨ 919 ≤ r → c₂.nreg r = d.nreg r := fun r hr => by
    rw [hK₂.nreg r (by simp; omega), gn₁ r (by pomega) (by pomega)]
  have hRW₂ : ∀ r < 752, c₂.nreg r ≤ W' := fun r hr => by
    rw [hA₂.nreg r (by simpa using hr)]; exact e₂s.wb_right.1 r
  have hMW₂ : ∀ a ≤ W', c₂.nmem a ≤ W' := fun a ha => by
    rw [hA₂.nmem a ha]; exact e₂s.wb_right.2 a
  have hrr₂ : c₂.rreg = c₁.rreg := by
    funext r
    by_cases hr : r < 752
    · rw [hA₂.rreg r (by simpa using hr), hcf₂.rreg, ← hA₁.rreg r (by simpa using hr)]
    · exact hK₂.rreg r (by simpa using hr)
  have hrm₂ : c₂.rmem = c₁.rmem := by
    funext a
    by_cases ha : a ≤ W'
    · rw [hA₂.rmem a ha, hcf₂.rmem, ← hA₁.rmem a ha]
    · exact hK₂.rmem a (by omega)
  have ho₂' : c₂.output = c₁.output := by rw [ho₂, hcf₂.out]; rfl
  -- 3. the input words copied to `Kw + 1`
  obtain ⟨c₃, t₃, e₃, ht₃, hcp₃, hk₃, hn₃, hrr₃, hrm₃, ho₃⟩ := cpyNProg_exec (P := I)
    (Dst := Kw + 1) (Src := β) (len := Kw + 1) (by pomega) (by pomega) (by pomega) (by pomega) c₂
    e₂.wb_right
  -- 4. Klein's real image cleared
  obtain ⟨c₄, t₄, e₄, ht₄, hf₄, hk₄, hn₄, hrr₄, hrm₄, ho₄⟩ := fillNProg_exec (P := I) (Dst := βK)
    (len := 2 * Kw + 2) (by pomega) (by pomega) c₃ e₃.wb_right
  -- 5. the residues of the constants copied to `βK`
  obtain ⟨c₅, t₅, e₅, ht₅, hcp₅, hk₅, hn₅, hrr₅, hrm₅, ho₅⟩ := cpyNProg_exec (P := I)
    (Dst := βK) (Src := RkN) (len := 3 * Fintype.card (Klein.SrcD fd.DQ fd.k) + 3) (by pomega) (by pomega) (by pomega) (by pomega) c₄
    e₄.wb_right
  -- 6. the registers of Klein's program cleared
  obtain ⟨c₆, t₆, e₆, ht₆, hz₆, hrr₆, hnm₆, hrm₆, ho₆⟩ :=
    zeroRegs_exec (P := I) (List.range 404) c₅ e₅.wb_right
  have hR₆ : ∀ r, (752 ≤ r ∧ r < 910) ∨ 919 ≤ r → c₆.nreg r = d.nreg r := fun r hr => by
    rw [hz₆ r, ite_eq_right_of_eq_false _ _ (eq_false (by simp; pomega)),
      hn₅ r (by pomega), hn₄ r (by pomega), hn₃ r (by pomega), hR₂ r hr]
  -- the memory up to here
  have hm₆ : ∀ a, (a < Kw + 1 ∨ 2 * Kw + 1 < a) → (a < Ys ∨ Ys + 3 * S ≤ a) →
      (a < βK ∨ βK + (2 * Kw + 1) < a) → c₆.nmem a = d.nmem a := fun a h1 h2 h3 => by
    rw [hnm₆, hk₅ a (by pomega), hk₄ a (by pomega), hk₃ a (by pomega), hm₂ a h2]
  have hcopy : ∀ i ≤ Kw, c₆.nmem (Kw + 1 + i) = Pk.data.getD i 0 := fun i hi => by
    rw [hnm₆, hk₅ _ (by pomega), hk₄ _ (by pomega), hcp₃ i (by pomega),
      hm₂ _ (by pomega)]
    exact hK.dat i hi
  -- 7. Klein's program on natural words
  have hE : Klein.KleinEncN (Klein.srcMap fd.inst.cycle) fd.k (Klein.srcG fd.inst.cycle)
      (Klein.srcPiece fd.k (fd.P'.image fd.e))
      (Klein.srcIso (V := fd.VQ) (F := fd.FQ) fd.k (fd.P'.image fd.e)
        (faceLen fd.P' fd.e (redLen N ℓ δ)) wt σ) σ Bw n (Kw + 1) (2 * Kw + 1) βK Mo Pk c₆ := by
    refine ⟨⟨by pomega, by pomega, rfl, hcopy⟩, fun a ha => ?_⟩
    by_cases h3 : a < 3 * Fintype.card (Klein.SrcD fd.DQ fd.k) + 3
    · rw [hnm₆, hcp₅ a h3, hk₄ _ (by pomega), hk₃ _ (by pomega), hm₂ _ (by pomega)]
      exact hK.res a h3
    · rw [hnm₆, hk₅ _ (by pomega), hf₄ a (by pomega), Klein.kConst_high (by pomega),
        Klein.resW_zero]
  obtain ⟨c₇, t₇, e₇, ht₇, hR₇, ho₇, hn₇, hk₇, hr₇, hrm₇, hw₇, hres₇⟩ :=
    fd_memN fd hq hk hnn hv₀ hHc
      (β := Kw + 1) (WK := 2 * Kw + 1) (βK := βK) (WN := WN) (by pomega) (by pomega) hN1 hWc I c₆
      e₆.wb_right
      (fun r hr => by rw [hz₆ r, ite_eq_left_of_eq_true _ _ (eq_true (by simp; omega))])
      (fun a ha => by
        by_cases h : a ≤ Kw
        · rw [hm₆ a (by pomega) (by pomega) (by pomega)]; exact (hlow a h).trans (by pomega)
        · obtain ⟨i, rfl⟩ : ∃ i, a = Kw + 1 + i := ⟨a - (Kw + 1), by pomega⟩
          rw [hcopy i (by pomega)]; exact (hP i).trans (by pomega))
      (fun a ha => by rw [hm₆ a (by pomega) (by pomega) (by pomega)]; exact hlow a ha) hE
  have hQ₇ : ∀ r, (752 ≤ r ∧ r < 910) ∨ 919 ≤ r → c₇.nreg r = d.nreg r := fun r hr => by
    rw [hn₇ r (by pomega), hR₆ r hr]
  have hm₇ : ∀ a, (a < Kw + 1 ∨ 2 * Kw + 1 < a) → (a < Ys ∨ Ys + 3 * S ≤ a) →
      (a < βK ∨ βK + (2 * Kw + 1) < a) → Kw < a → c₇.nmem a = d.nmem a := fun a h1 h2 h3 h4 => by
    rw [hk₇ a h4 (by pomega), hm₆ a h1 h2 h3]
  -- 8. the registers of `rdProgN`
  obtain ⟨c₈, t₈, e₈, ht₈, q300, q301, q302, q303, q304, q305, q306, q307, q308, q309, gn₈, gnm₈,
    grr₈, grm₈, go₈⟩ := kpRN_exec (P := I) (k := fd.k) (n := n)
      (OUTb := βK + Klein.aOUT (Fintype.card (Klein.SrcD fd.DQ fd.k))) (βN := βN) (M := M) c₇
      e₇.wb_right (by pomega) (by pomega) (by unfold Klein.aOUT; pomega) (by pomega) (by pomega)
      (by rw [hQ₇ 966 (by pomega), r966]; pomega) (by rw [hQ₇ 964 (by pomega), r964]; pomega)
  -- 9. the reading
  let R : RdN := ⟨b, fd.k, w, Ys + 2 * S, Ys + S, βN + δb, n,
    βK + Klein.aOUT (Fintype.card (Klein.SrcD fd.DQ fd.k)), Ys + 3 * S, βN + (Ys + 3 * S), M,
    fun s => c₂.nmem (Ys + 2 * S + s), fun s => ν (β' s)⟩
  have hc₈₂ : ∀ a, Kw < a → (a < Kw + 1 ∨ 2 * Kw + 1 < a) → (a < βK ∨ βK + (2 * Kw + 1) < a) →
      c₈.nmem a = c₂.nmem a := fun a h1 h2 h3 => by
    rw [gnm₈, hk₇ a h1 (by pomega), hnm₆, hk₅ a (by pomega), hk₄ a (by pomega), hk₃ a (by pomega)]
  have hRL : RdNLay R Mo WN := by
    refine ⟨fun s hs => (hS₂ s hs).1, fun s hs => hN.lt _ (bdry_sub_verts (hen.mem s hs)),
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals dsimp only [R]
    all_goals try unfold Klein.aOUT
    all_goals pomega
  have hRI : RdNIn R c₈ := by
    refine ⟨?_, ?_, ?_, ?_, q304, q305, q306, ?_, ?_, q309, fun s hs => ?_, fun s hs => ?_⟩
    · rw [q300, hQ₇ 802 (by pomega), r802]
    · rw [q301, hQ₇ 963 (by pomega), r963]
    · rw [q302, hQ₇ 962 (by pomega), r962]
    · rw [q303, hQ₇ 966 (by pomega), r966]
    · rw [q307, hQ₇ 964 (by pomega), r964]
    · rw [q308, hQ₇ 964 (by pomega), r964]
    · dsimp only [R] at hs ⊢; exact hc₈₂ _ (by pomega) (by pomega) (by pomega)
    · dsimp only [R] at hs ⊢; rw [hc₈₂ _ (by pomega) (by pomega) (by pomega)]; exact hO₂ s hs
  have hV : ∀ a < R.k * R.k, c₈.nmem (R.OUTb + a) ≤ Mo := fun a ha => by
    dsimp only [R] at ha ⊢
    rw [gnm₈, Nat.add_assoc]
    exact (hres₇ _ (by unfold Klein.aOUT; pomega)).le
  have hδ₈ : ∀ x < R.w, c₈.nmem (R.D0 + x) < R.M := fun x hx => by
    dsimp only [R] at hx ⊢
    rw [hc₈₂ _ (by pomega) (by pomega) (by pomega), hm₂ _ (by pomega)]
    exact (hδ x hx).lt hM0
  obtain ⟨c₉, t₉, e₉, ht₉, hO₉, hk₉, hreg₉, hrr₉, hrm₉, ho₉⟩ :=
    rdProgN_exec (P := I) hRL c₈ e₈.wb_right hRI hV hδ₈
  have hk₉' : ∀ a, (a < Ys + 3 * S ∨ Ys + 3 * S + b * b ≤ a) →
      (a < βN + (Ys + 3 * S) ∨ βN + (Ys + 3 * S) + b * b ≤ a) → c₉.nmem a = c₈.nmem a := hk₉
  -- 10. the scratch registers cleared
  obtain ⟨c₁₀, t₁₀, e₁₀, ht₁₀, hz₁₀, hrr₁₀, hnm₁₀, hrm₁₀, ho₁₀⟩ :=
    zeroRegs_exec (P := I) (List.range 408 ++ List.range' 910 9) c₉ e₉.wb_right
  have hz₁₀' : ∀ r, ¬ (r < 408 ∨ (910 ≤ r ∧ r < 919)) → c₁₀.nreg r = c₉.nreg r := fun r hr => by
    have : r ∉ List.range 408 ++ List.range' 910 9 := by simp only [List.mem_append, List.mem_range, List.mem_range'_1]; omega
    rw [hz₁₀ r, ite_eq_right_of_eq_false _ _ (eq_false this)]
  refine ⟨c₁₀, t₁ + (t₂ + (t₃ + (t₄ + (t₅ + (t₆ + (t₇ + (t₈ + (t₉ + t₁₀)))))))), β',
    Exec.seq e₁ (Exec.seq e₂ (Exec.seq e₃ (Exec.seq e₄ (Exec.seq e₅ (Exec.seq e₆
      (Exec.seq e₇ (Exec.seq e₈ (Exec.seq e₉ e₁₀)))))))), ?_, hen, fun x hx => ?_,
    hcr hmssp hnn, fun s hs t ht => ?_, fun r hr => ?_, fun a h1 h2 h3 h4 => ?_, ?_, ?_,
    fun a ha => ?_, ?_, fun r hr => ?_, fun r hr => ?_, fun a ha => ?_⟩
  · -- the cost
    simp only [List.length_range, List.length_append, List.length_range'] at ht₆ ht₁₀
    have h7 : t₇ ≤ 12 * (32886 * 2372500000 * P.card * lg P.card) + 14 * (fd.k * fd.k) + 12 :=
      ht₇
    have h9 : t₉ ≤ 36 * (b * b) + 5 := ht₉
    unfold partNCost
    pomega
  · -- the order
    rw [hnm₁₀, hk₉' _ (Or.inl (by pomega)) (Or.inl (by pomega)), hc₈₂ _ (by pomega) (by pomega)
      (by pomega)]
    exact hO₂ x hx
  · -- the matrices
    obtain ⟨hF, hL'⟩ := hO₉ s hs t ht
    have hF' : c₉.nmem (Ys + 3 * S + (s * b + t)) = R.flag c₈ s t := hF
    have hL'' : c₉.nmem (βN + (Ys + 3 * S + (s * b + t))) = R.val c₈ s t := by
      rw [← Nat.add_assoc]; exact hL'
    have hsB := hen.mem s hs
    have htB := hen.mem t ht
    have hνs := hN.lt _ (bdry_sub_verts hsB)
    have hνt := hN.lt _ (bdry_sub_verts htB)
    obtain ⟨i, hi, hib, hK'⟩ := hR₇ (β' s) hsB
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
    -- the natural answer read by `rdProgN`
    have hko : Klein.kOutNK (Fintype.card (Klein.SrcD fd.DQ fd.k)) n fd.k βK c₇ (R.σ s)
        (R.σ t) = if c₇.nmem (n + (R.σ s * fd.k + R.σ t)) = 1 then
          some (c₇.nmem (βK + Klein.aOUT (Fintype.card (Klein.SrcD fd.DQ fd.k)) +
            (R.σ s * fd.k + R.σ t)) : ℤ) else none := by
      unfold Klein.kOutNK Klein.aRB
      simp only [Nat.add_assoc]
    rw [hK'', ← hms] at hko
    have hfl : R.flag c₈ s t = if c₇.nmem (n + (R.σ s * fd.k + R.σ t)) = 1 then 1 else 0 := by
      unfold RdN.flag RdN.ad; rw [gnm₈]
    have hδs8 : c₈.nmem (R.D0 + R.ν s) = d.nmem (βN + δb + ν (β' s)) := by
      show c₈.nmem (βN + δb + ν (β' s)) = _
      rw [hc₈₂ _ (by pomega) (by pomega) (by pomega), hm₂ _ (by pomega)]
    have hδt8 : c₈.nmem (R.D0 + R.ν t) = d.nmem (βN + δb + ν (β' t)) := by
      show c₈.nmem (βN + δb + ν (β' t)) = _
      rw [hc₈₂ _ (by pomega) (by pomega) (by pomega), hm₂ _ (by pomega)]
    have hval : R.val c₈ s t = if c₇.nmem (n + (R.σ s * fd.k + R.σ t)) = 1 then
        (c₇.nmem (βK + Klein.aOUT (Fintype.card (Klein.SrcD fd.DQ fd.k)) +
          (R.σ s * fd.k + R.σ t)) + d.nmem (βN + δb + ν (β' t)) + M -
          d.nmem (βN + δb + ν (β' s))) % M else 0 := by
      unfold RdN.val
      rw [hδs8, hδt8]
      unfold RdN.ad; rw [gnm₈]
    have hδs := hδ (ν (β' s)) hνs
    have hδt := hδ (ν (β' t)) hνt
    rw [hN.inv _ (bdry_sub_verts hsB)] at hδs
    rw [hN.inv _ (bdry_sub_verts htB)] at hδt
    have hlen : (childDDG N mssp X ℓ δ (bdry N P₀ P₁)).len (β' s) (β' t) =
        (mssp X (redLen N ℓ δ) (bdry N P₀ P₁) (β' s) (β' t)).map
          (· + (δ (β' t) - δ (β' s))) := rfl
    rw [hnm₁₀]
    refine ⟨?_, ?_⟩
    · rw [hF', hfl]
      unfold finB arcOf
      rw [hlen, hko]
      by_cases h1 : c₇.nmem (n + (R.σ s * fd.k + R.σ t)) = 1
      · simp [h1]
      · simp [h1]
    · rw [hL'', hval]
      unfold matOf
      rw [hlen, hko]
      split_ifs with h1
      · simp only [Option.map_some, Option.getD_some]
        have e1 : ((c₇.nmem (βK + Klein.aOUT (Fintype.card (Klein.SrcD fd.DQ fd.k)) +
            (R.σ s * fd.k + R.σ t)) : ℤ)).toNat = c₇.nmem (βK +
              Klein.aOUT (Fintype.card (Klein.SrcD fd.DQ fd.k)) + (R.σ s * fd.k + R.σ t)) := by
          simp
        rw [← e1]
        exact res_shift hM0 (Int.natCast_nonneg _) hδt hδs (hδs.lt hM0)
      · simp only [Option.map_none, Option.getD_none, Int.cast_zero]
        exact_mod_cast ModNat.res_nat (M := M) (z := 0) hM0
  · -- the registers
    rw [hz₁₀' r (by pomega), hreg₉ r (by pomega), gn₈ r (by pomega)]; exact hQ₇ r hr
  · -- the memory
    rw [hnm₁₀, hk₉' a (by pomega) (by pomega), gnm₈]
    exact hm₇ a (by pomega) (by pomega) (by pomega) (by pomega)
  · rw [hrr₁₀, hrr₉, grr₈, hr₇, hrr₆, hrr₅, hrr₄, hrr₃, hrr₂, grr₁]
  · rw [hrm₁₀, hrm₉, grm₈, hrm₇, hrm₆, hrm₅, hrm₄, hrm₃, hrm₂, grm₁]
  · rw [hnm₁₀, hk₉' a (Or.inl (by pomega)) (Or.inl (by pomega)), gnm₈]
    by_cases h : a ≤ Kw
    · exact hw₇ a h
    · rw [hk₇ a (by pomega) (Or.inl ha)]
      obtain ⟨i, rfl⟩ : ∃ i, a = Kw + 1 + i := ⟨a - (Kw + 1), by pomega⟩
      rw [hcopy i (by pomega)]; exact hP i
  · rw [ho₁₀, ho₉, go₈, ho₇, ho₆, ho₅, ho₄, ho₃, ho₂', go₁]
  · rw [hz₁₀ r, ite_eq_left_of_eq_true _ _ (eq_true (by simp only [List.mem_append, List.mem_range, List.mem_range'_1]; omega))]
  · by_cases h4 : r < 408
    · rw [hz₁₀ r, ite_eq_left_of_eq_true _ _ (eq_true (by simp; omega))]; exact Nat.zero_le _
    · rw [hz₁₀' r (by pomega), hreg₉ r (by pomega), gn₈ r (by pomega), hn₇ r (by pomega),
        hz₆ r, ite_eq_right_of_eq_false _ _ (eq_false (by simp; pomega)), hn₅ r (by pomega),
        hn₄ r (by pomega), hn₃ r (by pomega)]
      exact hRW₂ r hr
  · rw [hnm₁₀]
    by_cases hF : Ys + 3 * S ≤ a ∧ a < Ys + 3 * S + b * b
    · obtain ⟨e', rfl⟩ : ∃ e', a = Ys + 3 * S + e' := ⟨a - (Ys + 3 * S), by omega⟩
      have he' : e' < b * b := by omega
      have hb0 : 0 < b := by
        rcases Nat.eq_zero_or_pos b with h | h
        · rw [h] at he'; simp at he'
        · exact h
      have hs : e' / b < b := Nat.div_lt_of_lt_mul he'
      have ht : e' % b < b := Nat.mod_lt _ hb0
      have hfl := (hO₉ (e' / b) hs (e' % b) ht).1
      have e1 : e' / b * b + e' % b = e' := by rw [Nat.mul_comm]; exact Nat.div_add_mod e' b
      have hfl' : c₉.nmem (Ys + 3 * S + e') = R.flag c₈ (e' / b) (e' % b) := by
        have : R.Fb + (e' / b * R.b + e' % b) = Ys + 3 * S + e' := by
          show Ys + 3 * S + (e' / b * b + e' % b) = _; rw [e1]
        rw [← this]; exact hfl
      rw [hfl']
      unfold RdN.flag
      split_ifs <;> pomega
    · rw [hk₉' a (by pomega) (Or.inl (by pomega)), gnm₈]
      by_cases h1 : a ≤ Kw
      · exact (hw₇ a h1).trans (by pomega)
      · by_cases h2 : a ≤ 2 * Kw + 1
        · rw [hk₇ a (by pomega) (Or.inl h2)]
          obtain ⟨i, rfl⟩ : ∃ i, a = Kw + 1 + i := ⟨a - (Kw + 1), by pomega⟩
          rw [hcopy i (by pomega)]; exact (hP i).trans (by pomega)
        · rw [hk₇ a (by pomega) (Or.inr (Or.inl (by pomega))), hnm₆, hk₅ a (by pomega),
            hk₄ a (by pomega), hk₃ a (by pomega)]
          exact hMW₂ a ha

end NegSSSP

end PlanarFlow
