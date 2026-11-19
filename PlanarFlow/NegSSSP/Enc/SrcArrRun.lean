module

public import PlanarFlow.NegSSSP.Enc.SrcArrA

/-!
# The dart arrays of the map with the sources copied: the whole run

* `srcArrProg_exec`: **`srcArrProg` (natural words only) writes, within
  `43 nD + 284 k + 45` steps, the words `semT` of every dart of the map with the sources copied**
  (`RV`, `NF`, `NE`, `NG`, `NT`, `NH`, `IS`, `LN = 0`, the `ED` word of its edge node, and the
  length with the sources copied at `SLb`), `GB[i] = srcNum (srcG i)` and the target nodes `XN[i]`,
  from the plain arrays of `M`, `g` and the lengths.
* `srcArr_kinput`: **any input whose words agree with the memory written (from `β`) meets the
  fields `Klein.KInputNL` and `Klein.KBnd`** of the map with the sources copied, for the layout
  `cLayout (srcVNum νv₀) (srcNum σ₀) (srcFNum τ₀)` (a `Klein.Layout`), and holds the target
  nodes of `Klein.KTgt.xn`; `srcArr_len`: the lengths with the sources copied at `SLb`, as
  `encResProg_fd` reads them.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace NegSSSP

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs Klein

variable {P : Input} {W : ℕ}

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F] {M : CombMap D V F} {k : ℕ} {g : ℕ → D} {S : Finset D} {ℓ : D → ℤ}
  {σ₀ : D ≃ Fin (Fintype.card D)} {νv₀ : V ≃ Fin (Fintype.card V)}
  {τ₀ : F ≃ Fin (Fintype.card F)}

lemma lay_weak {x β y E E' : ℕ} (d : x ≤ β ∨ E ≤ y) (h : E' ≤ E) : x ≤ β ∨ E' ≤ y := by
  omega

lemma lay_weak' {x β E E' : ℕ} (d : x < β ∨ E ≤ x) (h : E' ≤ E) : x < β ∨ E' ≤ x := by
  omega

set_option maxHeartbeats 4000000 in
/-- **The dart arrays of the map with the sources copied, on natural words** (see the module
docstring). Inputs: the plain arrays `QRV`, `QNT`, `QNF`, `QIS`, `QLN` of `M` by `σ₀` and `QG`
(the darts of the face cycle), placed apart from the writes `[β, β + 9 N + 14 ae + 2 k + 4)` and
`[SLb, SLb + N)`; the registers `2300 … 2311`. -/
theorem srcArrProg_exec (hf : MSSP.FaceCycle M k g) (hnn : ∀ d ∈ S, 0 ≤ ℓ d)
    {β SLb QRVb QNTb QNFb QISb QLNb QGb N a ae : ℕ}
    (hN : N = Fintype.card D + 8 * k) (ha : a = Fintype.card V + 2 * k)
    (hae : ae = a + N + (Fintype.card F + 2 * k))
    (hW : β + 9 * N + 14 * ae + 2 * k + 4 ≤ W) (hS : SLb + N ≤ W)
    (hSd : SLb + N ≤ β ∨ β + 9 * N + 14 * ae + 2 * k + 4 ≤ SLb)
    (q1 : QRVb + Fintype.card D ≤ W) (q2 : QNTb + Fintype.card D ≤ W)
    (q3 : QNFb + Fintype.card D ≤ W) (q4 : QISb + Fintype.card D ≤ W)
    (q5 : QLNb + Fintype.card D ≤ W) (q6 : QGb + k ≤ W)
    (d1 : QRVb + Fintype.card D ≤ β ∨ β + 9 * N + 14 * ae + 2 * k + 4 ≤ QRVb)
    (d2 : QNTb + Fintype.card D ≤ β ∨ β + 9 * N + 14 * ae + 2 * k + 4 ≤ QNTb)
    (d3 : QNFb + Fintype.card D ≤ β ∨ β + 9 * N + 14 * ae + 2 * k + 4 ≤ QNFb)
    (d4 : QISb + Fintype.card D ≤ β ∨ β + 9 * N + 14 * ae + 2 * k + 4 ≤ QISb)
    (d5 : QLNb + Fintype.card D ≤ β ∨ β + 9 * N + 14 * ae + 2 * k + 4 ≤ QLNb)
    (d6 : QGb + k ≤ β ∨ β + 9 * N + 14 * ae + 2 * k + 4 ≤ QGb)
    (e1 : QRVb + Fintype.card D ≤ SLb ∨ SLb + N ≤ QRVb)
    (e2 : QNTb + Fintype.card D ≤ SLb ∨ SLb + N ≤ QNTb)
    (e3 : QNFb + Fintype.card D ≤ SLb ∨ SLb + N ≤ QNFb)
    (e4 : QISb + Fintype.card D ≤ SLb ∨ SLb + N ≤ QISb)
    (e5 : QLNb + Fintype.card D ≤ SLb ∨ SLb + N ≤ QLNb)
    (e6 : QGb + k ≤ SLb ∨ SLb + N ≤ QGb)
    (hSW : (srcW S ℓ).toNat ≤ W)
    (c : Config) (hc : WordsBounded W c) (h00 : c.nreg 2300 = Fintype.card D)
    (h01 : c.nreg 2301 = k) (h02 : c.nreg 2302 = Fintype.card V)
    (h03 : c.nreg 2303 = Fintype.card F) (h04 : c.nreg 2304 = β) (h05 : c.nreg 2305 = SLb)
    (h06 : c.nreg 2306 = QRVb) (h07 : c.nreg 2307 = QNTb) (h08 : c.nreg 2308 = QNFb)
    (h09 : c.nreg 2309 = QISb) (h10 : c.nreg 2310 = QLNb) (h11 : c.nreg 2311 = QGb)
    (hQRV : ∀ d, c.nmem (QRVb + σ₀ d) = σ₀ (M.rev d))
    (hQNT : ∀ d, c.nmem (QNTb + σ₀ d) = νv₀ (M.tail d))
    (hQNF : ∀ d, c.nmem (QNFb + σ₀ d) = τ₀ (M.face d))
    (hQIS : ∀ d, c.nmem (QISb + σ₀ d) = if d ∈ S then 1 else 0)
    (hQLN : ∀ d, c.nmem (QLNb + σ₀ d) = (ℓ d).toNat)
    (hQG : ∀ i < k, c.nmem (QGb + i) = σ₀ (g i)) :
    ∃ c' t, Exec P W srcArrProg c c' t ∧ t ≤ 43 * Fintype.card D + 284 * k + 45 ∧
      (∀ d : SrcD D k, DWT β N ae a SLb c'.nmem (semT M k g S ℓ σ₀ νv₀ τ₀ (a + N) d) ∧
        c'.nmem (β + N + (semT M k g S ℓ σ₀ νv₀ τ₀ (a + N) d).x) =
          (semT M k g S ℓ σ₀ νv₀ τ₀ (a + N) d).fc) ∧
      (∀ i < k, c'.nmem (β + 8 * N + 2 * ae + i) = Fintype.card D + 8 * i ∧
        c'.nmem (β + 9 * N + 14 * ae + k + 4 + i) = νv₀ (M.tail (g i))) ∧
      (∀ x, (x < β ∨ β + 9 * N + 14 * ae + 2 * k + 4 ≤ x) → (x < SLb ∨ SLb + N ≤ x) →
        c'.nmem x = c.nmem x) ∧
      (∀ r, r < 2320 ∨ 2399 < r → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hk2 := hf.two_le
  -- the reads of the inputs outside the writes
  have hE : β + 8 * N + ae + N ≤ β + 9 * N + 14 * ae + 2 * k + 4 := by
    clear d1 d2 d3 d4 d5 d6 e1 e2 e3 e4 e5 e6 hSd; omega
  have r6 := fun x (hx : x < k) => lay_in d6 e6 hx
  have r3 := fun x (hx : x < Fintype.card D) => lay_in d3 e3 hx
  have hSd' : SLb + N ≤ β ∨ β + 8 * N + ae + N ≤ SLb := lay_weak hSd hE
  have d1' := lay_weak d1 hE
  have d2' := lay_weak d2 hE
  have d3' := lay_weak d3 hE
  have d4' := lay_weak d4 hE
  have d5' := lay_weak d5 hE
  have hacc := accF_full (σ₀ := σ₀) hnn
  have hSW' : (srcW S ℓ).toNat = accF S ℓ σ₀ (Fintype.card D) + 1 := by
    rw [← hacc]; rfl
  -- 1. the layout registers
  obtain ⟨c₁, k₁, e₁, hk₁, hR₁, i20, i22, i23, i30, i33, i34, i35, i49, i50, i51, i52, in₁, im₁,
      irr₁, irm₁, io₁⟩ :=
    saInit_exec (P := P) hN ha hae c hc h00 h01 h02 h03 h04 h05 hW
      (by clear d1 d2 d3 d4 d5 d6 e1 e2 e3 e4 e5 e6 hSd; omega)
  -- 2. the original darts
  obtain ⟨c₂, k₂, e₂, hk₂, ho₂, acc₂, j51, jm₂, jn₂, jrr₂, jrm₂, jo₂⟩ :=
    saOrig_exec (P := P) (M := M) (S := S) (ℓ := ℓ) (σ₀ := σ₀) (νv₀ := νv₀) (τ₀ := τ₀)
      (fo := a + N) (by omega) (by omega) hS (by omega) hSd' q1 q2 q3 q4 q5 d1' d2' d3' d4' d5'
      e1 e2 e3 e4 e5 (by omega) (by omega) c₁ e₁.wb_right
      (by rw [in₁ _ (by decide), h00]) (by rw [in₁ _ (by decide), h06])
      (by rw [in₁ _ (by decide), h07]) (by rw [in₁ _ (by decide), h08])
      (by rw [in₁ _ (by decide), h09]) (by rw [in₁ _ (by decide), h10]) i20 i33 hR₁ i51 i52
      (fun d => by rw [im₁]; exact hQRV d) (fun d => by rw [im₁]; exact hQNT d)
      (fun d => by rw [im₁]; exact hQNF d) (fun d => by rw [im₁]; exact hQIS d)
      (fun d => by rw [im₁]; exact hQLN d)
  have g2 : ∀ r, r ≠ 2351 → r ≠ 2352 → (r < 2390 ∨ 2399 < r) → c₂.nreg r = c₁.nreg r := jn₂
  have hg0 := (σ₀ (g 0)).2
  have hf0 := (τ₀ (M.face (g 0))).2
  have mg0 : c₂.nmem QGb = σ₀ (g 0) := by
    have := r6 0 (by omega)
    rw [Nat.add_zero] at this
    rw [jm₂ _ (lay_weak' this.1 hE) this.2, im₁]
    simpa using hQG 0 (by omega)
  have mf0 : c₂.nmem (QNFb + σ₀ (g 0)) = τ₀ (M.face (g 0)) := by
    have := r3 _ hg0
    rw [jm₂ _ (lay_weak' this.1 hE) this.2, im₁]
    exact hQNF _
  -- 3. between the loops
  obtain ⟨c₃, k₃, e₃, hk₃, m53, m85, m64, m65, m73, m77, mn₃, mm₃, mrr₃, mrm₃, mo₃⟩ :=
    saMid_exec (P := P) (acc := accF S ℓ σ₀ (Fintype.card D)) (QGb := QGb) (QNFb := QNFb)
      (fo := a + N) (nD := Fintype.card D) (nV := Fintype.card V)
      (fB := a + N + Fintype.card F) c₂ e₂.wb_right acc₂
      (by rw [g2 _ (by decide) (by decide) (by decide), i20])
      (by rw [g2 _ (by decide) (by decide) (by decide), in₁ _ (by decide), h11])
      (by rw [g2 _ (by decide) (by decide) (by decide), in₁ _ (by decide), h08])
      (by rw [g2 _ (by decide) (by decide) (by decide), i33])
      (by rw [g2 _ (by decide) (by decide) (by decide), in₁ _ (by decide), h00])
      (by rw [g2 _ (by decide) (by decide) (by decide), in₁ _ (by decide), h02])
      (by rw [g2 _ (by decide) (by decide) (by decide), i34])
      (by omega) (by rw [mg0]; omega) (by rw [mg0, mf0]; omega)
  rw [mg0, mf0] at m85
  have g3 : ∀ r, (r < 2351 ∨ (2353 < r ∧ r < 2364) ∨ 2399 < r) → c₃.nreg r = c₁.nreg r :=
    fun r hr => by
      rw [mn₃ r (by omega)]
      exact g2 r (by omega) (by omega) (by omega)
  -- 4. the added darts
  obtain ⟨c₄, k₄, e₄, hk₄, hw₄, hbx₄, hm₄, hn₄, hrr₄, hrm₄, ho₄⟩ :=
    saAdd_exec (P := P) (M := M) (S := S) (ℓ := ℓ) (σ₀ := σ₀) (νv₀ := νv₀) (τ₀ := τ₀) hf hN ha
      hae rfl hW hS hSd q2 q6 d2 d6 e2 e6 c₃ e₃.wb_right
      (hR₁.of_frame' fun r hr => g3 r (by omega))
      (by rw [g3 _ (by decide), in₁ _ (by decide), h01])
      (by rw [g3 _ (by decide), in₁ _ (by decide), h02])
      (by rw [g3 _ (by decide), in₁ _ (by decide), h07])
      (by rw [g3 _ (by decide), in₁ _ (by decide), h11]) (by rw [g3 _ (by decide), i20])
      (by rw [g3 _ (by decide), i22]) (by rw [g3 _ (by decide), i23])
      (by rw [g3 _ (by decide), i34]) (by rw [g3 _ (by decide), i49])
      (by rw [g3 _ (by decide), i50]) (by rw [m53, hSW']) (by rw [m85]; ring) m64 m65 m73
      m77
      (fun i hi => by
        have := r6 i hi
        rw [mm₃, jm₂ _ (lay_weak' this.1 hE) this.2, im₁]; exact hQG i hi)
      (fun d => by
        have := lay_in d2 e2 (σ₀ d).2
        rw [mm₃, jm₂ _ (lay_weak' this.1 hE) this.2, im₁]; exact hQNT d)
      (fun d => by rw [mm₃]; exact ho₂ d)
  refine ⟨c₄, _, .seq e₁ (.seq e₂ (.seq e₃ e₄)), by omega, hw₄, hbx₄, fun x hx1 hx2 => ?_,
    fun r hr => ?_, by rw [hrr₄, mrr₃, jrr₂, irr₁], by rw [hrm₄, mrm₃, jrm₂, irm₁],
    by rw [ho₄, mo₃, jo₂, io₁]⟩
  · rw [hm₄ x hx1 hx2, mm₃, jm₂ x (lay_weak' hx1 hE) hx2, im₁]
  · rw [hn₄ r (by omega), g3 r (by omega), in₁ r (by omega)]

/-- **The fields of Klein's input written by `srcArrProg`** (see the module docstring): for the
layout `cLayout (srcVNum νv₀) (srcNum σ₀) (srcFNum τ₀)` of the map with the sources copied, on
`n = 2 ae` nodes, every input agreeing with the memory from `β` on the first
`9 N + 14 ae + 2 k + 4` words meets `KInputNL`, `KBnd` and the target nodes of `KTgt`. -/
theorem srcArr_kinput (hf : MSSP.FaceCycle M k g) {β SLb N a ae : ℕ}
    (hN : N = Fintype.card D + 8 * k) (ha : a = Fintype.card V + 2 * k)
    (hae : ae = a + N + (Fintype.card F + 2 * k)) {m : ℕ → ℕ}
    (hw : ∀ d : SrcD D k, DWT β N ae a SLb m (semT M k g S ℓ σ₀ νv₀ τ₀ (a + N) d) ∧
      m (β + N + (semT M k g S ℓ σ₀ νv₀ τ₀ (a + N) d).x) =
        (semT M k g S ℓ σ₀ νv₀ τ₀ (a + N) d).fc)
    (hbx : ∀ i < k, m (β + 8 * N + 2 * ae + i) = Fintype.card D + 8 * i ∧
      m (β + 9 * N + 14 * ae + k + 4 + i) = νv₀ (M.tail (g i)))
    (Pk : Input) (hP : ∀ i < 9 * N + 14 * ae + 2 * k + 4, Pk.data.getD i 0 = m (β + i))
    (ℓ' : SrcD D k → ℤ) :
    KInputNL (srcMap hf) (srcPiece k S) ℓ' (srcNum σ₀) (fun x => srcVNum νv₀ x)
        (fun d => Fintype.card (SrcV V k) + eIx (srcMap hf) (srcNum σ₀) d)
        (fun y => Fintype.card (SrcV V k) + Fintype.card (SrcD D k) + srcFNum τ₀ y)
        (fun d => Fintype.card (SrcV V k) + Fintype.card (SrcD D k) + Fintype.card (SrcF F k) +
          eIx (srcMap hf) (srcNum σ₀) d) Pk ∧
      KBnd k (srcG hf) (srcNum σ₀)
        (2 * (Fintype.card (SrcV V k) + Fintype.card (SrcD D k) + Fintype.card (SrcF F k))) Pk ∧
      (∀ i < k, Pk.data.getD (iXT (Fintype.card (SrcD D k))
          (2 * (Fintype.card (SrcV V k) + Fintype.card (SrcD D k) + Fintype.card (SrcF F k)))
          k + i) 0 = (srcVNum (k := k) νv₀ (.inl (M.tail (g i))) : ℕ)) ∧
      Layout (srcMap hf)
        (2 * (Fintype.card (SrcV V k) + Fintype.card (SrcD D k) + Fintype.card (SrcF F k)))
        (fun x => srcVNum νv₀ x)
        (fun d => Fintype.card (SrcV V k) + eIx (srcMap hf) (srcNum σ₀) d)
        (fun y => Fintype.card (SrcV V k) + Fintype.card (SrcD D k) + srcFNum τ₀ y)
        (fun d => Fintype.card (SrcV V k) + Fintype.card (SrcD D k) + Fintype.card (SrcF F k) +
          eIx (srcMap hf) (srcNum σ₀) d) := by
  have cV : Fintype.card (SrcV V k) = a := by rw [card_srcV, ha]
  have cD : Fintype.card (SrcD D k) = N := by rw [card_srcD, hN]; ring
  have cF : Fintype.card (SrcF F k) = Fintype.card F + 2 * k := card_srcF
  have hn : 2 * (Fintype.card (SrcV V k) + Fintype.card (SrcD D k) + Fintype.card (SrcF F k)) =
      2 * ae := by rw [cV, cD, cF, hae]
  have hae' : Fintype.card (SrcV V k) + Fintype.card (SrcD D k) + Fintype.card (SrcF F k) = ae :=
    by rw [cV, cD, cF, hae]
  have hfo : Fintype.card (SrcV V k) + Fintype.card (SrcD D k) = a + N := by rw [cV, cD]
  have bd : ∀ d : SrcD D k, (srcNum σ₀ d : ℕ) < N ∧ (srcNum σ₀ (srcRev M k d) : ℕ) < N :=
    fun d => ⟨by have := (srcNum σ₀ d).2; omega, by have := (srcNum σ₀ (srcRev M k d)).2; omega⟩
  refine ⟨⟨fun d => ?_, fun d => ?_, fun d => ?_, fun d => ?_, fun d => ?_, fun d => ?_,
    fun d => ?_, fun d => ?_⟩, fun i hi => ?_, fun i hi => ?_, cLayout _ _ _⟩
  · obtain ⟨hx, hr⟩ := bd d
    rw [hP _ (by simp only [iRV]; omega)]
    simp only [iRV, Nat.zero_add]
    exact (hw d).1.wrv
  · obtain ⟨hx, hr⟩ := bd d
    rw [hP _ (by simp only [iNF]; omega)]
    simp only [iNF, cD, ← Nat.add_assoc, cV]
    exact (hw d).2
  · obtain ⟨hx, hr⟩ := bd d
    rw [hP _ (by simp only [iNE]; omega)]
    simp only [iNE, cD, cV, cF, eIx]
    rw [← Nat.add_assoc β, ← hae]
    exact (hw d).1.wne
  · obtain ⟨hx, hr⟩ := bd d
    rw [hP _ (by simp only [iNG]; omega)]
    simp only [iNG, cD, ← Nat.add_assoc, cV, eIx]
    exact (hw d).1.wng
  · obtain ⟨hx, hr⟩ := bd d
    rw [hP _ (by simp only [iNT]; omega)]
    simp only [iNT, cD, ← Nat.add_assoc]
    exact (hw d).1.wnt
  · obtain ⟨hx, hr⟩ := bd d
    rw [hP _ (by simp only [iNH]; omega)]
    simp only [iNH, cD, ← Nat.add_assoc]
    exact (hw d).1.wnh
  · obtain ⟨hx, hr⟩ := bd d
    rw [hP _ (by simp only [iIS]; omega)]
    simp only [iIS, cD, ← Nat.add_assoc, mem_srcPiece]
    exact (hw d).1.wis
  · obtain ⟨hx, hr⟩ := bd d
    have he : eIx (srcMap hf) (srcNum σ₀) d = (srcNum σ₀ d : ℕ) ∨
        eIx (srcMap hf) (srcNum σ₀) d = (srcNum σ₀ ((srcMap hf).rev d) : ℕ) := by
      unfold eIx; omega
    have hed : Pk.data.getD (iED (Fintype.card (SrcD D k)) + (Fintype.card (SrcV V k) +
        Fintype.card (SrcD D k) + Fintype.card (SrcF F k) + eIx (srcMap hf) (srcNum σ₀) d)) 0 =
        eIx (srcMap hf) (srcNum σ₀) d := by
      have hel : eIx (srcMap hf) (srcNum σ₀) d < N := by unfold eIx; omega
      rw [hP _ (by simp only [iED]; omega)]
      simp only [iED, cD, cV, cF, eIx]
      rw [← hae, ← Nat.add_assoc]
      exact (hw d).1.wed
    rw [hed]; exact he
  · rw [hP _ (by simp only [iGB]; omega)]
    simp only [iGB, cD]
    rw [show β + (8 * N + 2 * (Fintype.card (SrcV V k) + N + Fintype.card (SrcF F k)) + i) =
      β + 8 * N + 2 * ae + i by omega, (hbx i hi).1]
    simp [srcG, srcNum_inr, kindIdx, Nat.mod_eq_of_lt hi]
  · rw [hP _ (by simp only [iXT]; omega)]
    simp only [iXT, cD, srcVNum_inl]
    rw [show β + (9 * N + 7 * (2 * (Fintype.card (SrcV V k) + N + Fintype.card (SrcF F k))) + k +
      4 + i) = β + 9 * N + 14 * ae + k + 4 + i by omega]
    exact (hbx i hi).2

/-- The lengths with the sources copied at `SLb`, by the numbers of the darts. -/
lemma srcArr_len {β SLb N ae a : ℕ} {m : ℕ → ℕ}
    (hw : ∀ d : SrcD D k, DWT β N ae a SLb m (semT M k g S ℓ σ₀ νv₀ τ₀ (a + N) d))
    (d : SrcD D k) : m (SLb + srcNum σ₀ d) = (srcLen ℓ (srcW S ℓ) d).toNat :=
  (hw d).wsl

end NegSSSP

end PlanarFlow
