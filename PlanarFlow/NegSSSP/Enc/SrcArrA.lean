module

public import PlanarFlow.NegSSSP.Enc.SrcArr

/-!
# The dart arrays of the map with the sources copied: the added darts

`saAdd_exec`: the loop over the vertices `i < k` of the face writes the eight added darts of
every vertex (`semT`, by `semT_inr`), corrects the face nodes of the darts `g i` (whose face is
cut), and writes `GB[i] = srcNum (srcG i)` and `XN[i] = νv₀ (tail (g i))`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace NegSSSP

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs Klein

variable {P : Input} {W : ℕ}

section Add

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F] {M : CombMap D V F} {k : ℕ} {g : ℕ → D} {S : Finset D} {ℓ : D → ℤ}
  {σ₀ : D ≃ Fin (Fintype.card D)} {νv₀ : V ≃ Fin (Fintype.card V)}
  {τ₀ : F ≃ Fin (Fintype.card F)}

variable (M k g τ₀) in
/-- The face node of an original dart after the face vertices `i < r` are done. -/
noncomputable def fcO (r : ℕ) (d : D) : ℕ :=
  (gIdx k g d).elim (τ₀ (M.face d) : ℕ)
    (fun i => if (i : ℕ) < r then Fintype.card F + 2 * i else τ₀ (M.face d))

lemma fcO_zero (d : D) : fcO M k g τ₀ 0 d = τ₀ (M.face d) := by
  unfold fcO; cases gIdx k g d <;> simp

lemma fcO_k (d : D) : fcO M k g τ₀ k d = srcFNum τ₀ (srcFace M k g (.inl d)) := by
  unfold fcO
  rcases h : gIdx k g d with _ | i
  · simp [srcFace, h, srcFNum_inl]
  · simp [srcFace, h, srcFNum_inr, i.2]

lemma fcO_self (hf : MSSP.FaceCycle M k g) {r : ℕ} (hr : r < k) :
    fcO M k g τ₀ (r + 1) (g r) = Fintype.card F + 2 * r := by
  unfold fcO
  have := gIdx_g hf ⟨r, hr⟩
  simp only [Fin.val_mk] at this
  simp [this]

lemma fcO_other {r : ℕ} (hr : r < k) {d : D} (hd : d ≠ g r) :
    fcO M k g τ₀ (r + 1) d = fcO M k g τ₀ r d := by
  unfold fcO
  rcases h : gIdx k g d with _ | i
  · rfl
  · have hgi := gIdx_some h
    have hir : (i : ℕ) ≠ r := fun e => hd (by rw [← hgi, e])
    simp only [Option.elim]
    by_cases h1 : (i : ℕ) < r
    · simp [h1, show (i : ℕ) < r + 1 by omega]
    · simp [h1, show ¬ (i : ℕ) < r + 1 by omega]

lemma semT_ok {N fo : ℕ} (hN : N = Fintype.card D + 8 * k) (d : SrcD D k) :
    OkT N (semT M k g S ℓ σ₀ νv₀ τ₀ fo d) := by
  have h1 := (srcNum σ₀ d).2
  have h2 := (srcNum σ₀ (srcRev M k d)).2
  have e := card_srcD (D := D) k
  exact ⟨by simp only [semT]; omega, by simp only [semT]; omega⟩

lemma semT_x_inr (fo : ℕ) (i : Fin k) (κ : SrcKind) :
    (semT M k g S ℓ σ₀ νv₀ τ₀ fo (.inr (i, κ))).x = Fintype.card D + ((kindIdx κ : ℕ) + 8 * i) :=
  by simp [semT, srcNum_inr]

lemma dwt_upd3 {β N ae ag SLb : ℕ} {m : ℕ → ℕ} {w : WT} (h : DWT β N ae ag SLb m w)
    (hw : OkT N w) {y A2 A3 v1 v2 v3 : ℕ} (hy : y < N) (h2 : β + 8 * N + ae + N ≤ A2)
    (h3 : β + 8 * N + ae + N ≤ A3) (hS : SLb + N ≤ β ∨ β + 8 * N + ae + N ≤ SLb)
    (h2S : A2 < SLb ∨ SLb + N ≤ A2) (h3S : A3 < SLb ∨ SLb + N ≤ A3) :
    DWT β N ae ag SLb (upd (upd (upd m (β + N + y) v1) A2 v2) A3 v3) w := by
  obtain ⟨hx, hrv⟩ := hw
  obtain ⟨f0, f2, f3, f4, f5, f6, f7, f8, f9⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp (disch := omega) only [upd_other]; exact f0
  · simp (disch := omega) only [upd_other]; exact f2
  · simp (disch := omega) only [upd_other]; exact f3
  · simp (disch := omega) only [upd_other]; exact f4
  · simp (disch := omega) only [upd_other]; exact f5
  · simp (disch := omega) only [upd_other]; exact f6
  · simp (disch := omega) only [upd_other]; exact f7
  · simp (disch := omega) only [upd_other]; exact f8
  · simp (disch := omega) only [upd_other]; exact f9

/-- The words of the eight darts of the face vertex `r`. -/
noncomputable def saAddL (M : CombMap D V F) (k : ℕ) (g : ℕ → D) (S : Finset D) (ℓ : D → ℤ)
    (σ₀ : D ≃ Fin (Fintype.card D)) (νv₀ : V ≃ Fin (Fintype.card V))
    (τ₀ : F ≃ Fin (Fintype.card F)) (fo : ℕ) {r : ℕ} (hr : r < k) : List WT :=
  kinds.map fun κ => semT M k g S ℓ σ₀ νv₀ τ₀ fo (.inr (⟨r, hr⟩, κ))

lemma saAddL_eq (fo : ℕ) {r : ℕ} (hr : r < k) :
    kinds.map (addT (Fintype.card D + 8 * r) (Fintype.card V + 2 * r)
      (Fintype.card V + 2 * ((r + 1) % k)) (fo + Fintype.card F + 2 * r)
      (fo + Fintype.card F + 2 * ((r + k - 1) % k)) (νv₀ (M.tail (g r)))
      (fo + τ₀ (M.face (g 0))) (srcW S ℓ).toNat) = saAddL M k g S ℓ σ₀ νv₀ τ₀ fo hr := by
  unfold saAddL
  refine List.map_congr_left fun κ _ => ?_
  rw [semT_inr]

lemma mem_addL (fo : ℕ) {r : ℕ} (hr : r < k) (κ : SrcKind) :
    semT M k g S ℓ σ₀ νv₀ τ₀ fo (.inr (⟨r, hr⟩, κ)) ∈ saAddL M k g S ℓ σ₀ νv₀ τ₀ fo hr :=
  List.mem_map_of_mem (mem_kinds κ)

lemma saAddL_x {fo r : ℕ} (hr : r < k) {w : WT} (hw : w ∈ saAddL M k g S ℓ σ₀ νv₀ τ₀ fo hr) :
    Fintype.card D + 8 * r ≤ w.x ∧ w.x < Fintype.card D + 8 * r + 8 := by
  obtain ⟨κ, -, rfl⟩ := List.mem_map.1 hw
  rw [semT_x_inr]
  have := (kindIdx κ).2
  simp only [Fin.val_mk]
  omega

lemma saAddL_nodup (fo : ℕ) {r : ℕ} (hr : r < k) :
    ((saAddL M k g S ℓ σ₀ νv₀ τ₀ fo hr).map WT.x).Nodup := by
  unfold saAddL
  rw [List.map_map]
  refine List.Nodup.map (fun κ κ' h => ?_) (by decide)
  simp only [Function.comp, semT_x_inr, Fin.val_mk] at h
  exact kindEquiv.injective (Fin.ext (by simp only [kindEquiv, Equiv.coe_fn_mk]; omega))

/-! ### The memory after one face vertex -/

/-- The memory after the face vertex `r`: the eight darts, then the face node of `g r`,
`GB[r]`, `XN[r]`. -/
noncomputable def addMem (M : CombMap D V F) (k : ℕ) (g : ℕ → D) (S : Finset D) (ℓ : D → ℤ)
    (σ₀ : D ≃ Fin (Fintype.card D)) (νv₀ : V ≃ Fin (Fintype.card V))
    (τ₀ : F ≃ Fin (Fintype.card F)) (β N ae a SLb fo : ℕ) (m : ℕ → ℕ) {r : ℕ} (hr : r < k) :
    ℕ → ℕ :=
  upd (upd (upd (wrL β N ae a SLb m (saAddL M k g S ℓ σ₀ νv₀ τ₀ fo hr)) (β + N + σ₀ (g r))
    (fo + Fintype.card F + 2 * r)) (β + 8 * N + 2 * ae + r) (Fintype.card D + 8 * r))
    (β + 9 * N + 14 * ae + k + 4 + r) (νv₀ (M.tail (g r)))

/-- The memory part of the invariant of the loop over the face vertices. -/
structure AddMemInv (M : CombMap D V F) (k : ℕ) (g : ℕ → D) (S : Finset D) (ℓ : D → ℤ)
    (σ₀ : D ≃ Fin (Fintype.card D)) (νv₀ : V ≃ Fin (Fintype.card V))
    (τ₀ : F ≃ Fin (Fintype.card F)) (β N ae a SLb fo r : ℕ) (m : ℕ → ℕ) : Prop where
  orig : ∀ d, DWT β N ae a SLb m (oT M S ℓ σ₀ νv₀ τ₀ fo d) ∧
    m (β + N + σ₀ d) = fo + fcO M k g τ₀ r d
  add : ∀ i : Fin k, (i : ℕ) < r → ∀ κ,
    DWT β N ae a SLb m (semT M k g S ℓ σ₀ νv₀ τ₀ fo (.inr (i, κ))) ∧
    m (β + N + (semT M k g S ℓ σ₀ νv₀ τ₀ fo (.inr (i, κ))).x) =
      (semT M k g S ℓ σ₀ νv₀ τ₀ fo (.inr (i, κ))).fc
  bx : ∀ i < r, m (β + 8 * N + 2 * ae + i) = Fintype.card D + 8 * i ∧
    m (β + 9 * N + 14 * ae + k + 4 + i) = νv₀ (M.tail (g i))

section MemStep

variable {β N ae a SLb fo : ℕ}

set_option maxHeartbeats 1000000 in
lemma addMem_orig (hf : MSSP.FaceCycle M k g) (hN : N = Fintype.card D + 8 * k)
    (hNa : N ≤ ae) (hSd : SLb + N ≤ β ∨ β + 8 * N + ae + N ≤ SLb)
    (hA2S : ∀ r < k, β + 8 * N + 2 * ae + r < SLb ∨ SLb + N ≤ β + 8 * N + 2 * ae + r)
    (hA3S : ∀ r < k, β + 9 * N + 14 * ae + k + 4 + r < SLb ∨
      SLb + N ≤ β + 9 * N + 14 * ae + k + 4 + r)
    {m : ℕ → ℕ} {r : ℕ} (hr : r < k) (h : AddMemInv M k g S ℓ σ₀ νv₀ τ₀ β N ae a SLb fo r m)
    (d : D) :
    DWT β N ae a SLb (addMem M k g S ℓ σ₀ νv₀ τ₀ β N ae a SLb fo m hr)
        (oT M S ℓ σ₀ νv₀ τ₀ fo d) ∧
      addMem M k g S ℓ σ₀ νv₀ τ₀ β N ae a SLb fo m hr (β + N + σ₀ d) =
        fo + fcO M k g τ₀ (r + 1) d := by
  have hd0 := (σ₀ d).2
  have hgr := (σ₀ (g r)).2
  have hLx : ∀ w ∈ saAddL M k g S ℓ σ₀ νv₀ τ₀ fo hr, Fintype.card D ≤ w.x := fun w hw => by
    have := (saAddL_x hr hw).1; omega
  have hLok : ∀ w ∈ saAddL M k g S ℓ σ₀ νv₀ τ₀ fo hr, OkT N w := fun w hw => by
    obtain ⟨κ, -, rfl⟩ := List.mem_map.1 hw; exact semT_ok hN _
  have hdx : ∀ w ∈ saAddL M k g S ℓ σ₀ νv₀ τ₀ fo hr, w.x ≠ (oT M S ℓ σ₀ νv₀ τ₀ fo d).x :=
    fun w hw => by have := hLx w hw; simp only [oT]; omega
  have hok : OkT N (oT M S ℓ σ₀ νv₀ τ₀ fo d) := ⟨by simp only [oT]; omega,
    by simp only [oT]; have := (σ₀ (M.rev d)).2; omega⟩
  have hA2 : β + 8 * N + ae + N ≤ β + 8 * N + 2 * ae + r := by omega
  have hA3 : β + 8 * N + ae + N ≤ β + 9 * N + 14 * ae + k + 4 + r := by omega
  refine ⟨dwt_upd3 (dwT_wrL hSd hok _ _ (h.orig d).1 hLok hdx) hok (by omega) hA2 hA3 hSd
    (hA2S r hr) (hA3S r hr), ?_⟩
  unfold addMem
  rw [upd_other _ _ _ (show β + N + (σ₀ d : ℕ) ≠ β + 9 * N + 14 * ae + k + 4 + r by omega),
    upd_other _ _ _ (show β + N + (σ₀ d : ℕ) ≠ β + 8 * N + 2 * ae + r by omega)]
  by_cases hdg : d = g r
  · rw [hdg, upd_same, fcO_self hf hr]; omega
  · have hne : (σ₀ d : ℕ) ≠ σ₀ (g r) := fun e => hdg (σ₀.injective (Fin.ext e))
    rw [upd_other _ _ _ (show β + N + (σ₀ d : ℕ) ≠ β + N + σ₀ (g r) by omega),
      nf_wrL hSd (by omega) _ _ hLok (fun w hw => by have := hLx w hw; omega),
      (h.orig d).2, fcO_other hr hdg]

set_option maxHeartbeats 1000000 in
lemma addMem_add (hN : N = Fintype.card D + 8 * k)
    (hNa : N ≤ ae) (hSd : SLb + N ≤ β ∨ β + 8 * N + ae + N ≤ SLb)
    (hA2S : ∀ r < k, β + 8 * N + 2 * ae + r < SLb ∨ SLb + N ≤ β + 8 * N + 2 * ae + r)
    (hA3S : ∀ r < k, β + 9 * N + 14 * ae + k + 4 + r < SLb ∨
      SLb + N ≤ β + 9 * N + 14 * ae + k + 4 + r)
    {m : ℕ → ℕ} {r : ℕ} (hr : r < k) (h : AddMemInv M k g S ℓ σ₀ νv₀ τ₀ β N ae a SLb fo r m)
    (i : Fin k) (hi : (i : ℕ) < r + 1) (κ : SrcKind) :
    DWT β N ae a SLb (addMem M k g S ℓ σ₀ νv₀ τ₀ β N ae a SLb fo m hr)
        (semT M k g S ℓ σ₀ νv₀ τ₀ fo (.inr (i, κ))) ∧
      addMem M k g S ℓ σ₀ νv₀ τ₀ β N ae a SLb fo m hr
          (β + N + (semT M k g S ℓ σ₀ νv₀ τ₀ fo (.inr (i, κ))).x) =
        (semT M k g S ℓ σ₀ νv₀ τ₀ fo (.inr (i, κ))).fc := by
  have hgr := (σ₀ (g r)).2
  have hLok : ∀ w ∈ saAddL M k g S ℓ σ₀ νv₀ τ₀ fo hr, OkT N w := fun w hw => by
    obtain ⟨κ, -, rfl⟩ := List.mem_map.1 hw; exact semT_ok hN _
  have hok := semT_ok (M := M) (g := g) (S := S) (ℓ := ℓ) (σ₀ := σ₀) (νv₀ := νv₀)
    (τ₀ := τ₀) (fo := fo) hN (.inr (i, κ))
  have hx := semT_x_inr (M := M) (g := g) (S := S) (ℓ := ℓ) (σ₀ := σ₀) (νv₀ := νv₀)
    (τ₀ := τ₀) fo i κ
  have hκ := (kindIdx κ).2
  have hA2 : β + 8 * N + ae + N ≤ β + 8 * N + 2 * ae + r := by omega
  have hA3 : β + 8 * N + ae + N ≤ β + 9 * N + 14 * ae + k + 4 + r := by omega
  have k1 : β + N + (semT M k g S ℓ σ₀ νv₀ τ₀ fo (.inr (i, κ))).x ≠ β + N + σ₀ (g r) := by
    omega
  have k2 : β + N + (semT M k g S ℓ σ₀ νv₀ τ₀ fo (.inr (i, κ))).x ≠
      β + 8 * N + 2 * ae + r := by omega
  have k3 : β + N + (semT M k g S ℓ σ₀ νv₀ τ₀ fo (.inr (i, κ))).x ≠
      β + 9 * N + 14 * ae + k + 4 + r := by omega
  unfold addMem
  rw [upd_other _ _ _ k3, upd_other _ _ _ k2, upd_other _ _ _ k1]
  by_cases hir : (i : ℕ) = r
  · have hi' : i = ⟨r, hr⟩ := Fin.ext hir
    rw [hi'] at hok ⊢
    obtain ⟨w1, w2⟩ := wrL_dwT (ag := a) hSd _ m (mem_addL fo hr κ) (saAddL_nodup fo hr) hLok
    exact ⟨dwt_upd3 w1 hok (by omega) hA2 hA3 hSd (hA2S r hr) (hA3S r hr), w2⟩
  · have hir' : (i : ℕ) < r := by omega
    obtain ⟨w1, w2⟩ := h.add i hir' κ
    have hdx : ∀ w ∈ saAddL M k g S ℓ σ₀ νv₀ τ₀ fo hr,
        w.x ≠ (semT M k g S ℓ σ₀ νv₀ τ₀ fo (.inr (i, κ))).x :=
      fun w hw => by have := (saAddL_x hr hw).1; omega
    refine ⟨dwt_upd3 (dwT_wrL hSd hok _ _ w1 hLok hdx) hok (by omega) hA2 hA3 hSd
      (hA2S r hr) (hA3S r hr), ?_⟩
    rw [nf_wrL hSd hok.1 _ _ hLok hdx]
    exact w2

lemma addMem_bx (hNa : N ≤ ae) (hSd : SLb + N ≤ β ∨ β + 8 * N + ae + N ≤ SLb)
    (hA2S : ∀ r < k, β + 8 * N + 2 * ae + r < SLb ∨ SLb + N ≤ β + 8 * N + 2 * ae + r)
    (hA3S : ∀ r < k, β + 9 * N + 14 * ae + k + 4 + r < SLb ∨
      SLb + N ≤ β + 9 * N + 14 * ae + k + 4 + r)
    (hN : N = Fintype.card D + 8 * k)
    {m : ℕ → ℕ} {r : ℕ} (hr : r < k) (h : AddMemInv M k g S ℓ σ₀ νv₀ τ₀ β N ae a SLb fo r m)
    (i : ℕ) (hi : i < r + 1) :
    addMem M k g S ℓ σ₀ νv₀ τ₀ β N ae a SLb fo m hr (β + 8 * N + 2 * ae + i) =
        Fintype.card D + 8 * i ∧
      addMem M k g S ℓ σ₀ νv₀ τ₀ β N ae a SLb fo m hr (β + 9 * N + 14 * ae + k + 4 + i) =
        νv₀ (M.tail (g i)) := by
  have hgr := (σ₀ (g r)).2
  have hLok : ∀ w ∈ saAddL M k g S ℓ σ₀ νv₀ τ₀ fo hr, OkT N w := fun w hw => by
    obtain ⟨κ, -, rfl⟩ := List.mem_map.1 hw; exact semT_ok hN _
  unfold addMem
  by_cases hir : i = r
  · subst hir
    refine ⟨?_, upd_same _ _ _⟩
    rw [upd_other _ _ _ (by omega), upd_same]
  · obtain ⟨w1, w2⟩ := h.bx i (by omega)
    refine ⟨?_, ?_⟩
    · rw [upd_other _ _ _ (show β + 8 * N + 2 * ae + i ≠ β + 9 * N + 14 * ae + k + 4 + r by
        omega), upd_other _ _ _ (show β + 8 * N + 2 * ae + i ≠ β + 8 * N + 2 * ae + r by omega),
        upd_other _ _ _ (show β + 8 * N + 2 * ae + i ≠ β + N + σ₀ (g r) by omega),
        wrL_other hSd (by omega) (hA2S i (by omega)) _ _ hLok]
      exact w1
    · rw [upd_other _ _ _ (show β + 9 * N + 14 * ae + k + 4 + i ≠
          β + 9 * N + 14 * ae + k + 4 + r by omega),
        upd_other _ _ _ (show β + 9 * N + 14 * ae + k + 4 + i ≠ β + 8 * N + 2 * ae + r by
          omega),
        upd_other _ _ _ (show β + 9 * N + 14 * ae + k + 4 + i ≠ β + N + σ₀ (g r) by omega),
        wrL_other hSd (by omega) (hA3S i (by omega)) _ _ hLok]
      exact w2

lemma addMem_other (hN : N = Fintype.card D + 8 * k)
    (hSd : SLb + N ≤ β ∨ β + 8 * N + ae + N ≤ SLb) {m : ℕ → ℕ} {r : ℕ} (hr : r < k)
    {x : ℕ} (hx1 : x < β ∨ β + 9 * N + 14 * ae + 2 * k + 4 ≤ x) (hx2 : x < SLb ∨ SLb + N ≤ x) :
    addMem M k g S ℓ σ₀ νv₀ τ₀ β N ae a SLb fo m hr x = m x := by
  have hgr := (σ₀ (g r)).2
  have hLok : ∀ w ∈ saAddL M k g S ℓ σ₀ νv₀ τ₀ fo hr, OkT N w := fun w hw => by
    obtain ⟨κ, -, rfl⟩ := List.mem_map.1 hw; exact semT_ok hN _
  unfold addMem
  rw [upd_other _ _ _ (by omega), upd_other _ _ _ (by omega), upd_other _ _ _ (by omega),
    wrL_other hSd (by omega) hx2 _ _ hLok]

end MemStep

/-! ### The loop over the face vertices -/

set_option maxHeartbeats 4000000 in
/-- **One face vertex**: head, eight darts, tail. -/
theorem saBody_exec {β SLb N a ae fo QNTb QGb r : ℕ} (hr : r < k)
    (hX : Fintype.card D + 8 * r + 8 ≤ N) (hNa : N ≤ ae) (haN : a + N ≤ ae)
    (hW : β + 9 * N + 14 * ae + 2 * k + 4 ≤ W) (hS : SLb + N ≤ W)
    (hFB : fo + Fintype.card F + 2 * k ≤ ae) (hVB : Fintype.card V + 2 * k ≤ ae)
    (q2 : QNTb + Fintype.card D ≤ W) (q6 : QGb + k ≤ W)
    (c : Config) (hc : WordsBounded W c) (hR : WrRegs β N ae a SLb c)
    (h01 : c.nreg 2301 = k) (h02 : c.nreg 2302 = Fintype.card V)
    (h07 : c.nreg 2307 = QNTb) (h11 : c.nreg 2311 = QGb) (h20 : c.nreg 2320 = 1)
    (h22 : c.nreg 2322 = 8) (h23 : c.nreg 2323 = 2)
    (h34 : c.nreg 2334 = fo + Fintype.card F) (h49 : c.nreg 2349 = β + 8 * N + 2 * ae)
    (h50 : c.nreg 2350 = β + 9 * N + 14 * ae + k + 4)
    (h53 : c.nreg 2353 = (srcW S ℓ).toNat) (h85 : c.nreg 2385 = fo + τ₀ (M.face (g 0)))
    (h64 : c.nreg 2364 = r) (h65 : c.nreg 2365 = Fintype.card D + 8 * r)
    (h73 : c.nreg 2373 = Fintype.card V + 2 * r) (h77 : c.nreg 2377 = fo + Fintype.card F + 2 * r)
    (gq : c.nmem (QGb + r) = σ₀ (g r)) (gt : c.nmem (QNTb + σ₀ (g r)) = νv₀ (M.tail (g r))) :
    ∃ c' t, Exec P W saBody c c' t ∧ t ≤ 282 ∧
      c'.nmem = addMem M k g S ℓ σ₀ νv₀ τ₀ β N ae a SLb fo c.nmem hr ∧
      c'.nreg 2364 = r + 1 ∧ c'.nreg 2365 = Fintype.card D + 8 * (r + 1) ∧
      c'.nreg 2373 = Fintype.card V + 2 * (r + 1) ∧
      c'.nreg 2377 = fo + Fintype.card F + 2 * (r + 1) ∧
      (∀ r', (r' < 2364 ∨ (2385 ≤ r' ∧ r' < 2390) ∨ 2399 < r') → c'.nreg r' = c.nreg r') ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hgr := (σ₀ (g r)).2
  have htg := (νv₀ (M.tail (g r))).2
  -- 1. the head
  obtain ⟨c₂, k₂, e₂, hk₂, a66, a67, a68, a69, a70, a71, a72, a74, a78, a75, a76, a79, a80,
      a84, a81, an₂, am₂, arr₂, arm₂, ao₂⟩ :=
    saHead_exec (P := P) (i := r) (k := k) (nV := Fintype.card V) (fB := fo + Fintype.card F)
      (QGb := QGb) (QNTb := QNTb) c hc h64 h65 h73 h77 h20 h01 h02 h34 h11 h07 (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by rw [gq]; omega)
  rw [gq] at a84 a81
  rw [gt] at a81
  have hR₂ : WrRegs β N ae a SLb c₂ := hR.of_frame' fun r' hr' => an₂ r' (by omega)
  -- 2. the eight darts
  obtain ⟨c₃, k₃, e₃, hk₃, am₃, an₃, arr₃, arm₃, ao₃⟩ :=
    saDarts_exec (P := P) (X0 := Fintype.card D + 8 * r) (V0 := Fintype.card V + 2 * r)
      (Vs0 := Fintype.card V + 2 * ((r + 1) % k)) (F0 := fo + Fintype.card F + 2 * r)
      (Fp0 := fo + Fintype.card F + 2 * ((r + k - 1) % k)) (TG := νv₀ (M.tail (g r)))
      (FG := fo + τ₀ (M.face (g 0))) (SW := (srcW S ℓ).toNat) c₂ e₂.wb_right hR₂
      (by rw [an₂ _ (by omega), h65]) a66 a67 a68 a69 a70 a71 a72
      (by rw [an₂ _ (by omega), h73]) a74 a75 a76 (by rw [an₂ _ (by omega), h77]) a78
      a79 a80 a81 (by rw [an₂ _ (by omega), h85]) (by rw [an₂ _ (by omega), h53])
      (by rw [an₂ _ (by omega), h20]) (by rw [an₂ _ (by omega), hR.z]) (by omega) (by omega)
      (by omega) (by omega)
  have f3 : ∀ r', r' < 2390 → c₃.nreg r' = c₂.nreg r' := fun r' h => an₃ r' (Or.inl h)
  -- 3. the tail
  obtain ⟨c₄, k₄, e₄, hk₄, am₄, b65, b73, b77, b64, bn₄, brr₄, brm₄, bo₄⟩ :=
    saTail_exec (P := P) (i := r) (X0 := Fintype.card D + 8 * r)
      (V0 := Fintype.card V + 2 * r) (F0 := fo + Fintype.card F + 2 * r) (bN := β + N)
      (gi := σ₀ (g r)) (bG := β + 8 * N + 2 * ae) (bX := β + 9 * N + 14 * ae + k + 4)
      (TG := νv₀ (M.tail (g r))) c₃ e₃.wb_right
      (by rw [f3 _ (by omega), an₂ _ (by omega)]; exact hR.b1)
      (by rw [f3 _ (by omega), a84]) (by rw [f3 _ (by omega), an₂ _ (by omega), h77])
      (by rw [f3 _ (by omega), an₂ _ (by omega), h49])
      (by rw [f3 _ (by omega), an₂ _ (by omega), h64])
      (by rw [f3 _ (by omega), an₂ _ (by omega), h65])
      (by rw [f3 _ (by omega), an₂ _ (by omega), h50]) (by rw [f3 _ (by omega), a81])
      (by rw [f3 _ (by omega), an₂ _ (by omega), h22])
      (by rw [f3 _ (by omega), an₂ _ (by omega), h23])
      (by rw [f3 _ (by omega), an₂ _ (by omega), h73])
      (by rw [f3 _ (by omega), an₂ _ (by omega), h20])
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  refine ⟨c₄, _, .seq e₂ (.seq e₃ e₄), by omega, ?_, b64, by rw [b65]; ring, by rw [b73]; ring,
    by rw [b77]; ring, fun r' hr' => ?_, by rw [brr₄, arr₃, arr₂], by rw [brm₄, arm₃, arm₂],
    by rw [bo₄, ao₃, ao₂]⟩
  · rw [am₄, am₃, am₂, saAddL_eq fo hr]; rfl
  · rw [bn₄ _ (by omega) (by omega) (by omega) (by omega) (by omega), an₃ _ (by omega),
      an₂ _ (by omega)]

/-- The invariant of the loop over the face vertices. -/
structure AddInv (M : CombMap D V F) (k : ℕ) (g : ℕ → D) (S : Finset D) (ℓ : D → ℤ)
    (σ₀ : D ≃ Fin (Fintype.card D)) (νv₀ : V ≃ Fin (Fintype.card V))
    (τ₀ : F ≃ Fin (Fintype.card F)) (β N ae a SLb fo r : ℕ) (c₀ c : Config) : Prop where
  mem : AddMemInv M k g S ℓ σ₀ νv₀ τ₀ β N ae a SLb fo r c.nmem
  frame : ∀ x, (x < β ∨ β + 9 * N + 14 * ae + 2 * k + 4 ≤ x) → (x < SLb ∨ SLb + N ≤ x) →
    c.nmem x = c₀.nmem x
  r65 : c.nreg 2365 = Fintype.card D + 8 * r
  r73 : c.nreg 2373 = Fintype.card V + 2 * r
  r77 : c.nreg 2377 = fo + Fintype.card F + 2 * r
  regs : ∀ r', (r' < 2364 ∨ (2385 ≤ r' ∧ r' < 2390) ∨ 2399 < r') → c.nreg r' = c₀.nreg r'
  rr : c.rreg = c₀.rreg
  rm : c.rmem = c₀.rmem
  out : c.output = c₀.output

set_option maxHeartbeats 4000000 in
/-- One step of the loop over the face vertices. -/
theorem saAdd_step (hf : MSSP.FaceCycle M k g) {β SLb N a ae fo QNTb QGb : ℕ}
    (hN : N = Fintype.card D + 8 * k) (ha : a = Fintype.card V + 2 * k)
    (hae : ae = a + N + (Fintype.card F + 2 * k)) (hfo : fo = a + N)
    (hW : β + 9 * N + 14 * ae + 2 * k + 4 ≤ W) (hS : SLb + N ≤ W)
    (hSd : SLb + N ≤ β ∨ β + 9 * N + 14 * ae + 2 * k + 4 ≤ SLb)
    (q2 : QNTb + Fintype.card D ≤ W) (q6 : QGb + k ≤ W)
    (d2 : QNTb + Fintype.card D ≤ β ∨ β + 9 * N + 14 * ae + 2 * k + 4 ≤ QNTb)
    (d6 : QGb + k ≤ β ∨ β + 9 * N + 14 * ae + 2 * k + 4 ≤ QGb)
    (e2 : QNTb + Fintype.card D ≤ SLb ∨ SLb + N ≤ QNTb)
    (e6 : QGb + k ≤ SLb ∨ SLb + N ≤ QGb)
    (c : Config) (hR : WrRegs β N ae a SLb c)
    (h01 : c.nreg 2301 = k) (h02 : c.nreg 2302 = Fintype.card V)
    (h07 : c.nreg 2307 = QNTb) (h11 : c.nreg 2311 = QGb) (h20 : c.nreg 2320 = 1)
    (h22 : c.nreg 2322 = 8) (h23 : c.nreg 2323 = 2)
    (h34 : c.nreg 2334 = fo + Fintype.card F) (h49 : c.nreg 2349 = β + 8 * N + 2 * ae)
    (h50 : c.nreg 2350 = β + 9 * N + 14 * ae + k + 4)
    (h53 : c.nreg 2353 = (srcW S ℓ).toNat) (h85 : c.nreg 2385 = fo + τ₀ (M.face (g 0)))
    (hQG : ∀ i < k, c.nmem (QGb + i) = σ₀ (g i))
    (hQNT : ∀ d, c.nmem (QNTb + σ₀ d) = νv₀ (M.tail d))
    (r : ℕ) (c₁ : Config) (hr : r < k) (hw₁ : WordsBounded W c₁) (hr64 : c₁.nreg 2364 = r)
    (hb : c₁.nreg 2301 = k) (hI : AddInv M k g S ℓ σ₀ νv₀ τ₀ β N ae a SLb fo r c c₁) :
    ∃ c' t, Exec P W saBody c₁ c' t ∧ t ≤ 282 ∧ c'.nreg 2364 = r + 1 ∧ c'.nreg 2301 = k ∧
      AddInv M k g S ℓ σ₀ νv₀ τ₀ β N ae a SLb fo (r + 1) c c' := by
  have hk2 := hf.two_le
  have gq : c₁.nmem (QGb + r) = σ₀ (g r) := by
    obtain ⟨l1, l2⟩ := lay_in d6 e6 hr
    rw [hI.frame _ l1 l2]; exact hQG r hr
  have gt : c₁.nmem (QNTb + σ₀ (g r)) = νv₀ (M.tail (g r)) := by
    obtain ⟨l1, l2⟩ := lay_in d2 e2 (σ₀ (g r)).2
    rw [hI.frame _ l1 l2]; exact hQNT _
  have hNa : N ≤ ae := by clear d2 d6 e2 e6 hSd; omega
  have hSd' : SLb + N ≤ β ∨ β + 8 * N + ae + N ≤ SLb := by clear d2 d6 e2 e6; omega
  have hA2S : ∀ r < k, β + 8 * N + 2 * ae + r < SLb ∨ SLb + N ≤ β + 8 * N + 2 * ae + r :=
    fun r hr => by clear d2 d6 e2 e6 hSd'; omega
  have hA3S : ∀ r < k, β + 9 * N + 14 * ae + k + 4 + r < SLb ∨
      SLb + N ≤ β + 9 * N + 14 * ae + k + 4 + r := fun r hr => by clear d2 d6 e2 e6 hSd'; omega
  clear d2 d6 e2 e6 hSd
  have g' : ∀ r', (r' < 2364 ∨ (2385 ≤ r' ∧ r' < 2390) ∨ 2399 < r') → ∀ v,
      c.nreg r' = v → c₁.nreg r' = v := fun r' h v e => (hI.regs r' h).trans e
  obtain ⟨c₂, k₂, e₂, hk₂, hm₂, b64, b65, b73, b77, bn, brr, brm, bo⟩ :=
    saBody_exec (P := P) (S := S) (ℓ := ℓ) (νv₀ := νv₀) (τ₀ := τ₀) (fo := fo) hr
      (by omega) hNa (by omega) hW hS (by omega) (by omega) q2 q6 c₁ hw₁
      (hR.of_frame' fun r' hr' => hI.regs r' (by omega))
      (g' _ (by decide) _ h01) (g' _ (by decide) _ h02) (g' _ (by decide) _ h07)
      (g' _ (by decide) _ h11) (g' _ (by decide) _ h20) (g' _ (by decide) _ h22)
      (g' _ (by decide) _ h23) (g' _ (by decide) _ h34) (g' _ (by decide) _ h49)
      (g' _ (by decide) _ h50) (g' _ (by decide) _ h53) (g' _ (by decide) _ h85) hr64
      hI.r65 hI.r73 hI.r77 gq gt
  refine ⟨c₂, k₂, e₂, hk₂, b64, by rw [bn _ (by omega)]; exact hb, ?_⟩
  refine ⟨⟨fun d => ?_, fun i hi κ => ?_, fun i hi => ?_⟩, fun x hx1 hx2 => ?_, b65, b73,
    b77, fun r' hr' => by rw [bn r' hr', hI.regs r' hr'], by rw [brr, hI.rr],
    by rw [brm, hI.rm], by rw [bo, hI.out]⟩
  · rw [hm₂]; exact addMem_orig hf hN hNa hSd' hA2S hA3S hr hI.mem d
  · rw [hm₂]; exact addMem_add hN hNa hSd' hA2S hA3S hr hI.mem i hi κ
  · rw [hm₂]; exact addMem_bx hNa hSd' hA2S hA3S hN hr hI.mem i hi
  · rw [hm₂, addMem_other hN hSd' hr hx1 hx2]; exact hI.frame x hx1 hx2


set_option maxHeartbeats 4000000 in
/-- **The added darts** (and the face nodes of the darts of the face cycle, `GB`, `XN`). -/
theorem saAdd_exec (hf : MSSP.FaceCycle M k g) {β SLb N a ae fo QNTb QGb : ℕ}
    (hN : N = Fintype.card D + 8 * k) (ha : a = Fintype.card V + 2 * k)
    (hae : ae = a + N + (Fintype.card F + 2 * k)) (hfo : fo = a + N)
    (hW : β + 9 * N + 14 * ae + 2 * k + 4 ≤ W) (hS : SLb + N ≤ W)
    (hSd : SLb + N ≤ β ∨ β + 9 * N + 14 * ae + 2 * k + 4 ≤ SLb)
    (q2 : QNTb + Fintype.card D ≤ W) (q6 : QGb + k ≤ W)
    (d2 : QNTb + Fintype.card D ≤ β ∨ β + 9 * N + 14 * ae + 2 * k + 4 ≤ QNTb)
    (d6 : QGb + k ≤ β ∨ β + 9 * N + 14 * ae + 2 * k + 4 ≤ QGb)
    (e2 : QNTb + Fintype.card D ≤ SLb ∨ SLb + N ≤ QNTb)
    (e6 : QGb + k ≤ SLb ∨ SLb + N ≤ QGb)
    (c : Config) (hc : WordsBounded W c) (hR : WrRegs β N ae a SLb c)
    (h01 : c.nreg 2301 = k) (h02 : c.nreg 2302 = Fintype.card V)
    (h07 : c.nreg 2307 = QNTb) (h11 : c.nreg 2311 = QGb) (h20 : c.nreg 2320 = 1)
    (h22 : c.nreg 2322 = 8) (h23 : c.nreg 2323 = 2)
    (h34 : c.nreg 2334 = fo + Fintype.card F) (h49 : c.nreg 2349 = β + 8 * N + 2 * ae)
    (h50 : c.nreg 2350 = β + 9 * N + 14 * ae + k + 4)
    (h53 : c.nreg 2353 = (srcW S ℓ).toNat) (h85 : c.nreg 2385 = fo + τ₀ (M.face (g 0)))
    (h64 : c.nreg 2364 = 0) (h65 : c.nreg 2365 = Fintype.card D)
    (h73 : c.nreg 2373 = Fintype.card V) (h77 : c.nreg 2377 = fo + Fintype.card F)
    (hQG : ∀ i < k, c.nmem (QGb + i) = σ₀ (g i))
    (hQNT : ∀ d, c.nmem (QNTb + σ₀ d) = νv₀ (M.tail d))
    (horig : ∀ d, DWT β N ae a SLb c.nmem (oT M S ℓ σ₀ νv₀ τ₀ fo d) ∧
      c.nmem (β + N + σ₀ d) = fo + τ₀ (M.face d)) :
    ∃ c' t, Exec P W saAdd c c' t ∧ t ≤ 284 * k + 2 ∧
      (∀ d : SrcD D k, DWT β N ae a SLb c'.nmem (semT M k g S ℓ σ₀ νv₀ τ₀ fo d) ∧
        c'.nmem (β + N + (semT M k g S ℓ σ₀ νv₀ τ₀ fo d).x) =
          (semT M k g S ℓ σ₀ νv₀ τ₀ fo d).fc) ∧
      (∀ i < k, c'.nmem (β + 8 * N + 2 * ae + i) = Fintype.card D + 8 * i ∧
        c'.nmem (β + 9 * N + 14 * ae + k + 4 + i) = νv₀ (M.tail (g i))) ∧
      (∀ x, (x < β ∨ β + 9 * N + 14 * ae + 2 * k + 4 ≤ x) → (x < SLb ∨ SLb + N ≤ x) →
        c'.nmem x = c.nmem x) ∧
      (∀ r, (r < 2364 ∨ (2385 ≤ r ∧ r < 2390) ∨ 2399 < r) → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hk2 := hf.two_le
  have hJ0 : AddInv M k g S ℓ σ₀ νv₀ τ₀ β N ae a SLb fo 0 c c :=
    ⟨⟨fun d => by rw [fcO_zero]; exact horig d, fun i hi => absurd hi (by omega),
      fun i hi => absurd hi (by omega)⟩, fun _ _ _ => rfl, by rw [h65]; rfl, by rw [h73]; rfl,
      by rw [h77]; rfl, fun _ _ => rfl, rfl, rfl, rfl⟩
  obtain ⟨c', t, ex, ht, hw', hJ⟩ := forLoop_exec (P := P) (W := W) (a := 2364) (bR := 2301)
    (body := saBody) (fun r c' => AddInv M k g S ℓ σ₀ νv₀ τ₀ β N ae a SLb fo r c c') (n := k)
    (K := 282) c hc h64 h01 hJ0
    (fun r c₁ hr hw₁ hr64 hb hI => saAdd_step hf hN ha hae hfo hW hS hSd q2 q6 d2 d6 e2 e6 c
      hR h01 h02 h07 h11 h20 h22 h23 h34 h49 h50 h53 h85 hQG hQNT r c₁ hr hw₁ hr64 hb hI)
  refine ⟨c', t, ex, by omega, fun d => ?_, hJ.mem.bx, hJ.frame, hJ.regs, hJ.rr, hJ.rm, hJ.out⟩
  rcases d with d | ⟨i, κ⟩
  · refine ⟨(dwt_oT d).2 (hJ.mem.orig d).1, ?_⟩
    have := (hJ.mem.orig d).2
    rw [fcO_k] at this
    simpa [semT, srcNum_inl] using this
  · exact hJ.mem.add i i.2 κ

end Add

end NegSSSP

end PlanarFlow
