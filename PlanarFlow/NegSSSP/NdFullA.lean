module

public import PlanarFlow.NegSSSP.NdGlue
public import PlanarFlow.NegSSSP.NdFullSplit
public import PlanarFlow.NegSSSP.Enc.SdArrK

/-!
# The full branch: the side arrays of one side

* **`SideOut`**: what the side arrays of one side leave (the positions of the sources on the
  face, at `T₀ + 2 (nV + nF) + vn (ψ b)`; the sizes `#DQ`, `#VQ`, `#FQ − 1`, `C.k` in four
  registers from `o`; the six plain arrays of the one-face instance of the side at `I0`, with
  the lengths `faceLen (side N K Z) (sideE hbd) (redLen N ℓ pot)`), **`SideOut.congr`**.
* `nD_le`: the instance of a side has at most `3 m'` darts.
* **`fbSide o …`** `= cpRegs (fbSL …) ; sdArr ; cpRegs (fbVL o)` and **`fbSide_exec`**: the side
  arrays from registers holding the layout (`sdArr_exec_k`), the sizes saved to `o … o + 3`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace NegSSSP

open Finset Function Equiv Orbit CombMap Relation PlanarSeparator PlanarSeparator.Map
  PlanarSeparator.StDart BKMNW WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs
  Monge.CmpAbs PlanarSeparator.MillerProg

universe u v w

variable {P : Input} {W : ℕ}

/-- The register copies before the side arrays of one side. -/
def fbSL (rD rSb rbL rT0 rsv rI0 : ℕ) : List (ℕ × ℕ) :=
  [(2750, 2474), (2751, 2208), (2752, 3003), (2753, 2214), (2754, rD), (2755, 2206),
    (2756, rSb), (2776, 960), (2777, rbL), (2778, 2474), (2779, 2215), (2780, 2216),
    (2781, rSb), (801, 2217), (2790, rT0), (2791, 2218), (2792, rsv), (2793, 2211),
    (2794, rbL), (2795, 2475), (2796, rI0)]

/-- The sizes saved after the side arrays. -/
def fbVL (o : ℕ) : List (ℕ × ℕ) := [(o, 2580), (o + 1, 2593), (o + 2, 2581), (o + 3, 2559)]

/-- **The side arrays of one side.** -/
def fbSide (rD rSb rbL rT0 rsv rI0 o : ℕ) : Stmt :=
  .seq (cpRegs (fbSL rD rSb rbL rT0 rsv rI0)) (.seq sdArr (cpRegs (fbVL o)))

theorem fbSide_natOnly (rD rSb rbL rT0 rsv rI0 o : ℕ) :
    Klein.natOnly (fbSide rD rSb rbL rT0 rsv rI0 o) = true := by
  have h1 := cpRegs_natOnly (fbSL rD rSb rbL rT0 rsv rI0)
  have h2 := cpRegs_natOnly (fbVL o)
  have h3 : Klein.natOnly sdArr = true := by kernel_rfl
  simp [fbSide, Klein.natOnly, h1, h2, h3]

section Side

variable {D : Type u} {V : Type v} {F : Type w} [Fintype D] [DecidableEq D] [Fintype V]
  [DecidableEq V] [Fintype F] [DecidableEq F] {N : CombMap D V F}

/-- **What the side arrays of one side leave** (see the module docstring). -/
def SideOut (K : Finset D) (C : (kst N K).SCycle) (Z : Finset (kst N K).Face)
    (hbd : ∀ δ, ((kst N K).face δ ∈ Z ↔ (kst N K).face ((kst N K).α δ) ∈ Z) ↔ ¬ C.Mem δ)
    (Bs : Finset V) (ψ : V → SVert (kσ N K) (rcl N K)) {nV : ℕ}
    (vn : SVert (kσ N K) (rcl N K) ≃ Fin nV) (nF : ℕ) (ℓ : D → ℤ) (pot : V → ℤ)
    (T₀ I0 o : ℕ) (c : Config) : Prop :=
  ∃ i₀ < C.k,
    (∀ b ∈ Bs, c.nmem (T₀ + 2 * (nV + nF) + vn (ψ b)) < C.k ∧
      (kst N K).vert ((discCyc C Z).d ((i₀ + c.nmem (T₀ + 2 * (nV + nF) + vn (ψ b))) %
        C.k)) = .inl (ψ b)) ∧
    ∃ (σ₀ : SDart (discDarts (kst N K) Z) ≃ Fin (Fintype.card (SDart (discDarts (kst N K) Z))))
      (νv₀ : SVert (dσ (kst N K) Z) (discDarts (kst N K) Z) ≃
        Fin (Fintype.card (SVert (dσ (kst N K) Z) (discDarts (kst N K) Z))))
      (τ₀ : SFace (dσ (kst N K) Z) (discDarts (kst N K) Z) (revPerm (combOfSep (kst N K))) ≃
        Fin (Fintype.card (SFace (dσ (kst N K) Z) (discDarts (kst N K) Z)
          (revPerm (combOfSep (kst N K)))))),
      c.nreg o = Fintype.card (SDart (discDarts (kst N K) Z)) ∧
      c.nreg (o + 1) = Fintype.card (SVert (dσ (kst N K) Z) (discDarts (kst N K) Z)) ∧
      c.nreg (o + 2) + 1 = Fintype.card (SFace (dσ (kst N K) Z) (discDarts (kst N K) Z)
        (revPerm (combOfSep (kst N K)))) ∧
      c.nreg (o + 3) = C.k ∧
      (∀ d, c.nmem (I0 + σ₀ d) = σ₀ ((discMap (kst N K) Z).rev d)) ∧
      (∀ d, c.nmem (I0 + Fintype.card (SDart (discDarts (kst N K) Z)) + σ₀ d) =
        νv₀ ((discMap (kst N K) Z).tail d)) ∧
      (∀ d, c.nmem (I0 + 2 * Fintype.card (SDart (discDarts (kst N K) Z)) + σ₀ d) =
        τ₀ ((discMap (kst N K) Z).face d)) ∧
      (∀ d, c.nmem (I0 + 3 * Fintype.card (SDart (discDarts (kst N K) Z)) + σ₀ d) =
        if d ∈ (side N K Z).image (sideE hbd) then 1 else 0) ∧
      (∀ d, c.nmem (I0 + 4 * Fintype.card (SDart (discDarts (kst N K) Z)) + σ₀ d) =
        (faceLen (side N K Z) (sideE hbd) (redLen N ℓ pot) d).toNat) ∧
      (∀ i < C.k, c.nmem (I0 + 5 * Fintype.card (SDart (discDarts (kst N K) Z)) + i) =
        σ₀ (discFace hbd i₀ i))

/-- **`SideOut` depends only on the positions, the arrays and the four size registers.** -/
theorem SideOut.congr {K : Finset D} {C : (kst N K).SCycle} {Z : Finset (kst N K).Face}
    {hbd : ∀ δ, ((kst N K).face δ ∈ Z ↔ (kst N K).face ((kst N K).α δ) ∈ Z) ↔ ¬ C.Mem δ}
    {Bs : Finset V} {ψ : V → SVert (kσ N K) (rcl N K)} {nV : ℕ}
    {vn : SVert (kσ N K) (rcl N K) ≃ Fin nV} {nF : ℕ} {ℓ : D → ℤ} {pot : V → ℤ}
    {T₀ I0 o : ℕ} {c c' : Config} (h : SideOut K C Z hbd Bs ψ vn nF ℓ pot T₀ I0 o c)
    (hp : ∀ a, T₀ + 2 * (nV + nF) ≤ a → a < T₀ + 2 * (nV + nF) + nV → c'.nmem a = c.nmem a)
    (ha : ∀ a, I0 ≤ a → a < I0 + 5 * Fintype.card (SDart (discDarts (kst N K) Z)) + C.k →
      c'.nmem a = c.nmem a)
    (hr : ∀ j < 4, c'.nreg (o + j) = c.nreg (o + j)) :
    SideOut K C Z hbd Bs ψ vn nF ℓ pot T₀ I0 o c' := by
  obtain ⟨i₀, hi₀, hpos, σ₀, νv₀, τ₀, a0, a1, a2, a3, aRV, aNT, aNF, aIS, aLN, aG⟩ := h
  have hσ : ∀ d, (σ₀ d : ℕ) < Fintype.card (SDart (discDarts (kst N K) Z)) := fun d => (σ₀ d).2
  have hv : ∀ b, (vn (ψ b) : ℕ) < nV := fun b => (vn (ψ b)).2
  have hr0 : c'.nreg o = c.nreg o := hr 0 (by omega)
  refine ⟨i₀, hi₀, fun b hb => ?_, σ₀, νv₀, τ₀, by rw [hr0]; exact a0,
    by rw [hr 1 (by omega)]; exact a1, by rw [hr 2 (by omega)]; exact a2,
    by rw [hr 3 (by omega)]; exact a3, fun d => ?_, fun d => ?_, fun d => ?_, fun d => ?_,
    fun d => ?_, fun i hi => ?_⟩
  · rw [hp _ (by omega) (by have := hv b; omega)]; exact hpos b hb
  · rw [ha _ (by omega) (by have := hσ d; omega)]; exact aRV d
  · rw [ha _ (by omega) (by have := hσ d; omega)]; exact aNT d
  · rw [ha _ (by omega) (by have := hσ d; omega)]; exact aNF d
  · rw [ha _ (by omega) (by have := hσ d; omega)]; exact aIS d
  · rw [ha _ (by omega) (by have := hσ d; omega)]; exact aLN d
  · rw [ha _ (by omega) (by omega)]; exact aG i hi

/-- **The instance of a side has at most `3 m'` darts.** -/
theorem nD_le {K : Finset D} {Z : Finset (kst N K).Face} {m' : ℕ}
    (cn : SDart (rcl N K) ≃ Fin m') : Fintype.card (SDart (discDarts (kst N K) Z)) ≤ 3 * m' := by
  have h1 : Fintype.card (SDart (discDarts (kst N K) Z)) ≤
      Fintype.card (StDart (SDart (rcl N K))) := Fintype.card_subtype_le _
  rw [StDart.card, Fintype.card_congr cn, Fintype.card_fin] at h1
  exact h1

variable {K : Finset D} {C : (kst N K).SCycle} {Z : Finset (kst N K).Face}

theorem fbVL_ok {o : ℕ} (ho : 2798 < o ∨ (840 < o ∧ o + 3 < 2550)) :
    cpOK (fbVL o) = true ∧ cpSrc (fbVL o) = true := by
  constructor
  · simp [fbVL, cpOK]
  · simp [fbVL, cpSrc]; omega

theorem fbVL_frame {o r : ℕ} (h : r < o ∨ o + 3 < r) : r ∉ (fbVL o).map (·.1) := by
  simp only [fbVL, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false]
  omega

theorem fbSL_frame {rD rSb rbL rT0 rsv rI0 r : ℕ} (h1 : r ≠ 801) (h2 : r < 2750 ∨ 2796 < r) :
    r ∉ (fbSL rD rSb rbL rT0 rsv rI0).map (·.1) := by
  simp only [fbSL, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false]
  omega

/-- The layout facts of `fbSide_exec` (a separate lemma: small `omega` contexts). -/
theorem fbSide_lay {Sb k m m' nV nF Ck W Lb h : ℕ} (hmk : m ≤ k) (hm'k : m' ≤ k)
    (hVF : nV + nF ≤ 2 * k) (hCk : Ck ≤ k) (dL : Lb + m ≤ Sb) (dT : h + k + m ≤ Sb)
    (hW : Sb + 60 * k + 5 ≤ W) :
    Sb + m ≤ Sb + k ∧ Sb + k + m' ≤ Sb + 2 * k ∧ (Sb + m ≤ Lb ∨ Lb + m ≤ Sb) ∧
      (Sb + m ≤ h ∨ h + m ≤ Sb) ∧ (Sb + m ≤ h + k ∨ h + k + m ≤ Sb) ∧ Lb + m ≤ W ∧
      h + m ≤ W ∧ h + k + m ≤ W ∧
      swA (Sb + 2 * k) m' nV nF k + 13 * m' + 2 * (nV + nF) ≤ Sb + 32 * k ∧
      Sb + 32 * k + 18 * m' + Ck + 5 ≤ W ∧ Sb ≤ W := by
  unfold swA
  refine ⟨by omega, by omega, Or.inr dL, Or.inr (by omega), Or.inr dT, by omega, by omega,
    by omega, by omega, by omega, by omega⟩

set_option maxHeartbeats 8000000 in
/-- **The side arrays of one side, the sizes saved** (see the module docstring). -/
theorem fbSide_exec (hrot : N.RotTrans) (hKr : K ⊆ reps N) {ψ : V → SVert (kσ N K) (rcl N K)}
    (hbd : ∀ δ, ((kst N K).face δ ∈ Z ↔ (kst N K).face ((kst N K).α δ) ∈ Z) ↔ ¬ C.Mem δ)
    {Bs : Finset V} (hBs : ∀ b ∈ Bs, Sum.inl (ψ b) ∈ C.verts)
    {Pc : Finset D} {m k : ℕ} {en : ℕ → D} {α σ : ℕ → ℕ} (he : PEnc N Pc m k en α σ)
    (hKP : K ⊆ Pc) (ℓ : D → ℤ) (pot : V → ℤ)
    {m' nV nF : ℕ} (cn : SDart (rcl N K) ≃ Fin m') (vn : SVert (kσ N K) (rcl N K) ≃ Fin nV)
    (fn : (kmap N K).Face ≃ Fin nF)
    {rD rSb rbL rT0 rsv rI0 o : ℕ}
    (hok : cpOK (fbSL rD rSb rbL rT0 rsv rI0) = true)
    (hsrc : cpSrc (fbSL rD rSb rbL rT0 rsv rI0) = true)
    (ho : 2798 < o ∨ (840 < o ∧ o + 3 < 2550))
    {Y bz sv bK Xb Fb Lb h Db M Sb : ℕ}
    (c₀ : Config) (hw : WordsBounded W c₀)
    (hE : Enc (kmap N K) cn vn fn c₀.nmem Y (Y + m') (Y + 2 * m') (Y + 3 * m') (Y + 4 * m'))
    (hz : ∀ x, ((kst N K).face (old x) ∈ Z ↔ c₀.nmem (bz + cn x) = sv))
    (hKB : ∀ x, c₀.nmem (bK + cn x) = if x.1 ∈ K then 1 else 0)
    (hXm : ∀ i < k, ∀ hm : en i ∈ rcl N K, c₀.nmem (Xb + i) = cn ⟨en i, hm⟩)
    (hFm : ∀ x < m, (c₀.nmem (Fb + x) ≠ 0 ↔ en x ∈ K))
    (hl : ∀ i < m, (c₀.nmem (Lb + i) : ℤ) = ℓ (en i) % M)
    (ht : ∀ i < m, (c₀.nmem (Db + c₀.nmem (h + i)) : ℤ) = pot (N.tail (en i)) % M)
    (hh : ∀ i < m, (c₀.nmem (Db + c₀.nmem (h + k + i)) : ℤ) = pot (N.head (en i)) % M)
    (hred : ∀ d ∈ side N K Z, 0 ≤ redLen N ℓ pot d ∧ redLen N ℓ pot d < M)
    (hCk : C.k ≤ k) (hM : 0 < M)
    -- the source registers of the copies
    (r74 : c₀.nreg 2474 = m) (r08 : c₀.nreg 2208 = Lb) (r03 : c₀.nreg 3003 = h)
    (r14 : c₀.nreg 2214 = h + k) (rDb : c₀.nreg rD = Db) (r06 : c₀.nreg 2206 = M)
    (rS : c₀.nreg rSb = Sb) (r960 : c₀.nreg 960 = m') (rL : c₀.nreg rbL = Sb + k)
    (r15 : c₀.nreg 2215 = Fb) (r16 : c₀.nreg 2216 = Xb) (r17 : c₀.nreg 2217 = Y)
    (rT : c₀.nreg rT0 = Sb + 2 * k) (r18 : c₀.nreg 2218 = bz) (rsv' : c₀.nreg rsv = sv)
    (r11 : c₀.nreg 2211 = bK) (r75 : c₀.nreg 2475 = k) (rI : c₀.nreg rI0 = Sb + 32 * k)
    (r961 : c₀.nreg 961 = nV) (r962 : c₀.nreg 962 = nF)
    -- the layout
    (hmk : m ≤ k) (hm'k : m' ≤ k) (hVF : nV + nF ≤ 2 * k)
    (hlo : Y + 5 * m' ≤ Sb ∧ bz + m' ≤ Sb ∧ bK + m' ≤ Sb ∧ Xb + k ≤ Sb ∧ Fb + m ≤ Sb)
    (dL : Lb + m ≤ Sb) (dT : h + k + m ≤ Sb)
    (hT : ∀ i < m, Db + c₀.nmem (h + i) < Sb) (hH : ∀ i < m, Db + c₀.nmem (h + k + i) < Sb)
    (hMW : 3 * M ≤ W) (hW : Sb + 60 * k + 5 ≤ W) (h6 : 6 ≤ W) :
    ∃ c' t, Exec P W (fbSide rD rSb rbL rT0 rsv rI0 o) c₀ c' t ∧
      t ≤ 33 * m + 405 * m' + 13 * (nV + nF) + 22 * C.k + 155 ∧
      SideOut K C Z hbd Bs ψ vn nF ℓ pot (Sb + 2 * k) (Sb + 32 * k) o c' ∧
      Sb + 32 * k + 5 * Fintype.card (SDart (discDarts (kst N K) Z)) + C.k ≤ Sb + 48 * k ∧
      (∀ a, (a < Sb ∨ Sb + 48 * k ≤ a) → c'.nmem a = c₀.nmem a) ∧
      (∀ r, r ≠ 10 → (r < 300 ∨ 318 < r) → (r < 800 ∨ 840 < r) → (r < 2550 ∨ 2593 < r) →
        (r < 2750 ∨ 2798 < r) → (r < o ∨ o + 3 < r) → c'.nreg r = c₀.nreg r) ∧
      c'.rreg = c₀.rreg ∧ c'.rmem = c₀.rmem ∧ c'.output = c₀.output := by
  have hnD := nD_le (Z := Z) cn
  -- the copies
  obtain ⟨c₁, e₁, g₁, f₁, m₁, rr₁, rm₁, o₁⟩ :=
    cpRegs_exec (P := P) (W := W) _ hok hsrc c₀ hw
  have G : ∀ p ∈ fbSL rD rSb rbL rT0 rsv rI0, c₁.nreg p.1 = c₀.nreg p.2 := g₁
  simp only [fbSL, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] at G
  obtain ⟨q50, q51, q52, q53, q54, q55, q56, q76, q77, q78, q79, q80, q81, q801, q90, q91, q92,
    q93, q94, q95, q96⟩ := G
  have F₁ : ∀ r, r ≠ 801 → (r < 2750 ∨ 2796 < r) → c₁.nreg r = c₀.nreg r := fun r h1 h2 =>
    f₁ r (fbSL_frame h1 h2)
  have hE₁ : Enc (kmap N K) cn vn fn c₁.nmem Y (Y + m') (Y + 2 * m') (Y + 3 * m')
      (Y + 4 * m') := by rw [m₁]; exact hE
  obtain ⟨L1, L2, L3, L4, L5, L6, L7, L8, L9, L10, L11⟩ :=
    fbSide_lay (Lb := Lb) (h := h) hmk hm'k hVF hCk dL dT hW
  obtain ⟨c₂, t₂, e₂, ht₂, i₀, hi₀, hpos, σ₀, νv₀, τ₀, a80, a93, a81, aRV, aNT, aNF, aIS, aLN,
      aG, a59, am, af, ar, arm, ao⟩ :=
    sdArr_exec_k (P := P) (W := W) (C := C) (Z := Z) hrot hKr hbd hBs he hKP ℓ pot cn vn fn
      (Y := Y) (bz := bz) (sv := sv) (bK := bK) (bL := Sb + k) (Xb := Xb) (Fb := Fb) (Lb := Lb)
      (Tb := h) (Hb := h + k) (Db := Db) (M := M) (Ob := Sb) (T₀ := Sb + 2 * k) (Ck := k)
      (I0 := Sb + 32 * k) c₁ e₁.wb_right hE₁
      (fun x => by rw [m₁]; exact hz x) (fun x => by rw [m₁]; exact hKB x)
      (fun i hi hm => by rw [m₁]; exact hXm i hi hm) (fun x hx => by rw [m₁]; exact hFm x hx)
      (fun i hi => by rw [m₁]; exact hl i hi) (fun i hi => by rw [m₁]; exact ht i hi)
      (fun i hi => by rw [m₁]; exact hh i hi) hred hCk hM
      (by rw [q50, r74]) (by rw [q51, r08]) (by rw [q52, r03]) (by rw [q53, r14])
      (by rw [q54, rDb]) (by rw [q55, r06]) (by rw [q56, rS]) (by rw [q76, r960])
      (by rw [q77, rL]) (by rw [q78, r74]) (by rw [q79, r15]) (by rw [q80, r16])
      (by rw [q81, rS]) (by rw [F₁ 960 (by omega) (by omega), r960])
      (by rw [F₁ 961 (by omega) (by omega), r961]) (by rw [F₁ 962 (by omega) (by omega), r962])
      (by rw [q801, r17]) (by rw [q90, rT]) (by rw [q91, r18]) (by rw [q92, rsv'])
      (by rw [q93, r11]) (by rw [q94, rL]) (by rw [q95, r75]) (by rw [q96, rI])
      hlo L1 L2 hmk L3 L4 L5
      (fun i hi => by rw [m₁]; have := hT i hi; exact ⟨by omega, Or.inl this⟩)
      (fun i hi => by rw [m₁]; have := hH i hi; exact ⟨by omega, Or.inl this⟩)
      L6 L7 L8 hMW L9 L10 h6
  -- the sizes
  obtain ⟨c₃, e₃, g₃, f₃, m₃, rr₃, rm₃, o₃⟩ :=
    cpRegs_exec (P := P) (W := W) (fbVL o) (fbVL_ok ho).1 (fbVL_ok ho).2 c₂ e₂.wb_right
  have G₃ : ∀ p ∈ fbVL o, c₃.nreg p.1 = c₂.nreg p.2 := g₃
  simp only [fbVL, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] at G₃
  obtain ⟨s0, s1, s2, s3⟩ := G₃
  have F₃ : ∀ r, (r < o ∨ o + 3 < r) → c₃.nreg r = c₂.nreg r := fun r h =>
    f₃ r (fbVL_frame h)
  have hnD5 : Sb + 32 * k + 5 * Fintype.card (SDart (discDarts (kst N K) Z)) + C.k ≤
      Sb + 48 * k := by clear * - hnD hm'k hCk; omega
  refine ⟨c₃, (fbSL rD rSb rbL rT0 rsv rI0).length + (t₂ + (fbVL o).length),
    .seq e₁ (.seq e₂ e₃), by clear * - ht₂; simp only [fbSL, fbVL, List.length_cons, List.length_nil]; omega, ?_, hnD5, fun a ha => ?_, fun r h1 h2 h3 h4 h5 h6 => ?_,
    by rw [rr₃, ar, rr₁], by rw [rm₃, arm, rm₁], by rw [o₃, ao, o₁]⟩
  · refine ⟨i₀, hi₀, fun b hb => ?_, σ₀, νv₀, τ₀, by rw [s0, a80], by rw [s1, a93],
      by rw [s2, a81], by rw [s3, a59], fun d => ?_, fun d => ?_, fun d => ?_, fun d => ?_,
      fun d => ?_, fun i hi => ?_⟩
    all_goals rw [m₃]
    · exact hpos b hb
    · exact aRV d
    · exact aNT d
    · exact aNF d
    · exact aIS d
    · exact aLN d
    · exact aG i hi
  · rw [m₃, am a (by omega), m₁]
  · rw [F₃ r h6, af r h1 h2 h3 h4 h5, F₁ r (by omega) (by omega)]

end Side

end NegSSSP

end PlanarFlow
