module

public import PlanarFlow.NegSSSP.NdFullMid2

/-!
# The full branch: the two one-face instances from the side arrays, with word bounds

* **`fdArr_le`**: every word of the plain arrays of an instance (`FdArr`) is at most
  `#DQ + #VQ + #FQ + srcW`;
* **`side_data'`**: `side_data` with the positions gathered modulo `k` for every vertex of `K`
  (as `fs_mid` leaves them) and the word bound of the copied arrays.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace NegSSSP

open Finset Function Equiv Orbit CombMap PlanarSeparator PlanarSeparator.Map
  PlanarSeparator.StDart BKMNW WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs
  PlanarSeparator.MillerProg

universe u v w

variable {D : Type u} {V : Type v} {F : Type w} [Fintype D] [DecidableEq D] [Fintype V]
  [DecidableEq V] [Fintype F] [DecidableEq F] {N : CombMap D V F}

theorem fdArr_le {X : Finset D} {Bs : Finset V} {fd : FaceData N X Bs}
    {σ : fd.DQ ≃ Fin (Fintype.card fd.DQ)} {νv : fd.VQ ≃ Fin (Fintype.card fd.VQ)}
    {τ : fd.FQ ≃ Fin (Fintype.card fd.FQ)} {ℓ : D → ℤ} {pot : V → ℤ} {mem : ℕ → ℕ} {I0 : ℕ}
    (h : FdArr fd σ νv τ ℓ pot mem I0) :
    ∀ j < 5 * Fintype.card fd.DQ + fd.k, mem (I0 + j) ≤ Fintype.card fd.DQ +
      Fintype.card fd.VQ + Fintype.card fd.FQ +
      (Klein.srcW (fd.P'.image fd.e) (faceLen fd.P' fd.e (redLen N ℓ pot))).toNat := by
  intro j hj
  have hσ : ∀ x, (σ x : ℕ) < Fintype.card fd.DQ := fun x => (σ x).2
  have hW := fun x => Int.toNat_le_toNat (faceLen_le_srcW fd (redLen N ℓ pot) x)
  have key : ∀ t < 5, ∀ r < Fintype.card fd.DQ, j = t * Fintype.card fd.DQ + r →
      mem (I0 + j) ≤ Fintype.card fd.DQ + Fintype.card fd.VQ + Fintype.card fd.FQ +
        (Klein.srcW (fd.P'.image fd.e) (faceLen fd.P' fd.e (redLen N ℓ pot))).toNat := by
    intro t ht r hr hj'
    obtain ⟨x, hrx⟩ : ∃ x, (σ x : ℕ) = r := ⟨σ.symm ⟨r, hr⟩, by simp⟩
    subst hrx
    interval_cases t
    · rw [hj', show 0 * Fintype.card fd.DQ + (σ x : ℕ) = σ x by ring, h.rv x]
      have := hσ (fd.Q.rev x); omega
    · rw [hj', show 1 * Fintype.card fd.DQ + (σ x : ℕ) = Fintype.card fd.DQ + σ x by ring,
        ← Nat.add_assoc, h.nt x]
      have := (νv (fd.Q.tail x)).2; omega
    · rw [hj', ← Nat.add_assoc, h.nf x]
      have := (τ (fd.Q.face x)).2; omega
    · rw [hj', ← Nat.add_assoc, h.is x]; split_ifs <;> omega
    · rw [hj', ← Nat.add_assoc, h.ln x]
      have := hW x; omega
  by_cases hj5 : j < 5 * Fintype.card fd.DQ
  · have h0 : 0 < Fintype.card fd.DQ := by omega
    exact key (j / Fintype.card fd.DQ) ((Nat.div_lt_iff_lt_mul h0).2 (by linarith))
      (j % Fintype.card fd.DQ) (Nat.mod_lt _ h0)
      (by rw [Nat.mul_comm]; exact (Nat.div_add_mod j _).symm)
  · have hi : j - 5 * Fintype.card fd.DQ < fd.k := by omega
    have e := h.g (j - 5 * Fintype.card fd.DQ) hi
    rw [show I0 + 5 * Fintype.card fd.DQ + (j - 5 * Fintype.card fd.DQ) = I0 + j by omega] at e
    rw [e]; have := hσ (fd.g (j - 5 * Fintype.card fd.DQ)); omega

/-- **`side_data` from the arrays `fs_mid` leaves** (positions modulo `k` for every vertex of
`K`), with the word bound of the copied arrays. -/
theorem side_data' (hM : N.IsPlane) (hrot : N.RotTrans) (hface : N.FaceTrans) {K : Finset D}
    (hKr : K ⊆ reps N) (hK0 : K.Nonempty) (hK : DConn N K) {ψ : V → SVert (kσ N K) (rcl N K)}
    (hψ : ∀ x : SDart (rcl N K), ψ (N.tail x.1) = (kmap N K).vert x)
    {C : (kst N K).SCycle} {Z : Finset (kst N K).Face}
    (hbd : ∀ δ, ((kst N K).face δ ∈ Z ↔ (kst N K).face ((kst N K).α δ) ∈ Z) ↔ ¬ C.Mem δ)
    {Bs : Finset V} (hBs : ∀ b ∈ Bs, b ∈ verts N (side N K Z) ∧ Sum.inl (ψ b) ∈ C.verts)
    {R : Finset D} (hR : Disjoint (verts N R) (verts N K)) {X : Finset D}
    (hX : X = side N K Z ∪ R) {nV : ℕ} {vn : SVert (kσ N K) (rcl N K) ≃ Fin nV} {nF : ℕ}
    {ℓ : D → ℤ} {pot : V → ℤ} {T₀ I0 o : ℕ} {c : Config}
    (hS : SideOut K C Z hbd Bs ψ vn nF ℓ pot T₀ I0 o c) {mem : ℕ → ℕ} {I0' Pb k : ℕ}
    {ν : V → ℕ}
    (hcp : ∀ j < 5 * Fintype.card (SDart (discDarts (kst N K) Z)) + C.k,
      mem (I0' + j) = c.nmem (I0 + j))
    (hps : ∀ x ∈ verts N K, mem (Pb + ν x) = c.nmem (T₀ + 2 * (nV + nF) + vn (ψ x)) % k)
    (hCk : C.k ≤ k) :
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
  have hps' : ∀ x ∈ Bs, mem (Pb + ν x) = c.nmem (T₀ + 2 * (nV + nF) + vn (ψ x)) := by
    intro x hx
    obtain ⟨i₀, -, hpos, -⟩ := hS
    rw [hps x (verts_mono (side_subset Z) (hBs x hx).1)]
    exact Nat.mod_eq_of_lt (lt_of_lt_of_le (hpos x hx).1 hCk)
  exact side_data hM hrot hface hKr hK0 hK hψ hbd hBs hR hX hS hcp hps'

theorem card_sVert_le {α : Type*} [Fintype α] [DecidableEq α] (σ : Equiv.Perm α)
    (B : Finset α) : Fintype.card (SVert σ B) ≤ Fintype.card (SDart B) := by
  rw [card_sVert, Fintype.card_coe]; exact nOrb_le_card σ B

theorem card_sFace_le {α : Type*} [Fintype α] [DecidableEq α] (σ ι : Equiv.Perm α)
    (B : Finset α) : Fintype.card (SFace σ B ι) ≤ Fintype.card (SDart B) := by
  rw [card_sFace, Fintype.card_coe]; exact nOrb_le_card _ B

theorem le_feIsoB (a b c W₀ : ℕ) : W₀ ≤ feIsoB a b c W₀ := by
  unfold feIsoB MSSP.isoN1 MSSP.isoN2 MSSP.isoN3
  have h1 : 1 ≤ (a * b + 1) * (2 * c * a + 1) * (a + 1) :=
    Nat.one_le_iff_ne_zero.2 (by positivity)
  have : W₀ ≤ (a * b + 1) * (2 * c * a + 1) * (a + 1) * W₀ := Nat.le_mul_of_pos_left _ h1
  omega

open Classical in
/-- **The weight bound of an instance** with lengths at most `3L` on the darts of `P'`. -/
theorem fb_srcW_le {DQ : Type u} [DecidableEq DQ] {P' : Finset D} {e : D → DQ} {ℓ' : D → ℤ} {L : ℕ}
    (hℓ : ∀ d ∈ P', ℓ' d ≤ 3 * L) :
    (Klein.srcW (P'.image e) (faceLen P' e ℓ')).toNat ≤ 1 + 3 * L * P'.card := by
  have hx : ∀ x ∈ P'.image e, faceLen P' e ℓ' x ≤ 3 * L := by
    intro x hx
    unfold faceLen
    rw [dif_pos (by obtain ⟨d, hd, rfl⟩ := Finset.mem_image.1 hx; exact ⟨d, hd, rfl⟩)]
    have hc := (show ∃ d ∈ P', e d = x by
      obtain ⟨d, hd, rfl⟩ := Finset.mem_image.1 hx; exact ⟨d, hd, rfl⟩).choose_spec.1
    exact max_le (by positivity) (hℓ _ hc)
  have hs : ∑ x ∈ P'.image e, faceLen P' e ℓ' x ≤ (P'.image e).card * (3 * L : ℤ) := by
    have := Finset.sum_le_sum hx
    simpa [Finset.sum_const, nsmul_eq_mul] using this
  have hci : ((P'.image e).card : ℤ) ≤ P'.card := by exact_mod_cast Finset.card_image_le
  have hnn : 0 ≤ ∑ x ∈ P'.image e, faceLen P' e ℓ' x :=
    Finset.sum_nonneg fun y _ => faceLen_nonneg P' e ℓ' y
  unfold Klein.srcW
  have h3 : ((P'.image e).card : ℤ) * (3 * L : ℤ) ≤ (P'.card : ℤ) * (3 * L : ℤ) :=
    mul_le_mul_of_nonneg_right hci (by positivity)
  have : (1 + ∑ x ∈ P'.image e, faceLen P' e ℓ' x).toNat ≤ ((1 + 3 * L * P'.card : ℕ) : ℤ).toNat := by
    apply Int.toNat_le_toNat; push_cast; nlinarith
  rwa [Int.toNat_natCast] at this

/-- **The sizes and the weight bound of a side** read from `SideOut`: `#VQ ≤ #DQ`,
`#FQ ≤ #DQ`, `#DQ ≤ 3m'`, the face length `C.k`, and the weight word
`1 + pwS (is) (ln) ≤ 1 + 3L · #side` when the reduced lengths on the side are at most `3L`. -/
theorem sideOut_facts {K : Finset D} {C : (kst N K).SCycle} {Z : Finset (kst N K).Face}
    {hbd : ∀ δ, ((kst N K).face δ ∈ Z ↔ (kst N K).face ((kst N K).α δ) ∈ Z) ↔ ¬ C.Mem δ}
    {Bs : Finset V} {ψ : V → SVert (kσ N K) (rcl N K)} {nV : ℕ}
    {vn : SVert (kσ N K) (rcl N K) ≃ Fin nV} {nF : ℕ} {ℓ : D → ℤ} {pot : V → ℤ}
    {T₀ I0 o : ℕ} {c : Config} (hS : SideOut K C Z hbd Bs ψ vn nF ℓ pot T₀ I0 o c) {m' L : ℕ}
    (cn : SDart (rcl N K) ≃ Fin m')
    (hred : ∀ x ∈ side N K Z, redLen N ℓ pot x ≤ 3 * L) :
    c.nreg (o + 1) ≤ c.nreg o ∧ c.nreg (o + 2) + 1 ≤ c.nreg o ∧ c.nreg o ≤ 3 * m' ∧
      c.nreg (o + 3) = C.k ∧
      1 + pwS c.nmem (I0 + 3 * c.nreg o) (I0 + 4 * c.nreg o) (c.nreg o) ≤
        1 + 3 * L * (side N K Z).card := by
  obtain ⟨i₀, -, -, σ₀, νv₀, τ₀, a0, a1, a2, a3, -, -, -, aIS, aLN, -⟩ := hS
  refine ⟨?_, ?_, ?_, a3, ?_⟩
  · rw [a0, a1]; exact card_sVert_le _ _
  · rw [a0, a2]; exact card_sFace_le _ _ _
  · rw [a0]; exact nD_le cn
  · rw [a0, pw_srcW σ₀ _ _ (fun x => faceLen_nonneg _ _ _ x) c.nmem _ _ aIS aLN]
    exact fb_srcW_le hred

/-- **The memory of the node's configuration** (the hypotheses `hz`, `hzc`, `hmW`, `hdm`,
`hres` of `fs_node`) from the written ranges, their word bounds, and the frame. -/
theorem fs_mem {mem cmem : ℕ → ℕ} {sp Z M₀ m w Y S I0₀ L₀ I0₁ L₁ E₁ W' M B WN Hb h k : ℕ}
    (hz0 : ∀ a ≤ sp, mem a = 0)
    (hF : ∀ a, sp < a → (a < Z ∨ Z + m ≤ a) → (a < Z + M₀ ∨ Z + M₀ + m ≤ a) →
      (a < Z + 2 * M₀ ∨ Z + 2 * M₀ + m ≤ a) → (a < I0₀ ∨ I0₀ + L₀ ≤ a) →
      (a < I0₁ ∨ I0₁ + L₁ ≤ a) → (a < Y + 16 * S ∨ Y + 16 * S + 2 * w ≤ a) →
      (a < W' + 1 + (Z + 3 * M₀) ∨ W' + 1 + (Z + 3 * M₀) + m ≤ a) →
      (a < W' + 1 + (Z + 4 * M₀) ∨ W' + 1 + (Z + 4 * M₀) + w ≤ a) →
      (a < W' + 1 + (Z + 5 * M₀) ∨ W' + 1 + (Z + 5 * M₀) + w ≤ a) →
      (a < h + 130 * k ∨ h + 156 * k ≤ a) → mem a = cmem a)
    (hc0 : ∀ a, sp < a → a < Hb → cmem a = 0)
    (hspZ : sp < Z) (hM₀ : M₀ = m + w + 1) (hY : Z + 22 * M₀ ≤ Y) (hI0₀ : I0₀ = Y + 16 * S + 2 * w)
    (hL₀ : I0₀ + L₀ ≤ I0₁) (hL₁ : I0₁ + L₁ ≤ E₁) (hEW : E₁ ≤ W') (hZW : Z + 6 * M₀ ≤ W')
    (hWN : 2 * W' + 1 + M ≤ WN) (hWHb : WN < Hb) (hHbh : Hb ≤ h) (hM : 0 < M)
    (vT : ∀ i < m, mem (Z + i) ≤ W') (vH : ∀ i < m, mem (Z + M₀ + i) ≤ W')
    (vS : ∀ i < m, mem (Z + 2 * M₀ + i) ≤ W') (vA0 : ∀ j < L₀, mem (I0₀ + j) ≤ W')
    (vA1 : ∀ j < L₁, mem (I0₁ + j) ≤ W') (vP : ∀ i < 2 * w, mem (Y + 16 * S + i) ≤ W')
    (vR : ∀ a, (W' + 1 + (Z + 3 * M₀) ≤ a ∧ a < W' + 1 + (Z + 3 * M₀) + m) ∨
      (W' + 1 + (Z + 4 * M₀) ≤ a ∧ a < W' + 1 + (Z + 4 * M₀) + w) ∨
      (W' + 1 + (Z + 5 * M₀) ≤ a ∧ a < W' + 1 + (Z + 5 * M₀) + w) →
      mem a < M ∧ (mem a ≤ B ∨ M ≤ mem a + B)) :
    (∀ a < Z, mem a = 0) ∧
    (∀ a ≤ WN, (a < Z ∨ E₁ ≤ a) → (a < W' + Z + 3 * M₀ + 1 ∨ W' + Z + 6 * M₀ + 1 ≤ a) →
      mem a = 0) ∧
    (∀ a ≤ W', mem a ≤ W') ∧ (∀ a ≤ WN, mem a ≤ WN) ∧
    (∀ a ≤ W', mem (W' + 1 + a) < M ∧ (mem (W' + 1 + a) ≤ B ∨ M ≤ mem (W' + 1 + a) + B)) := by
  -- a cell below `Hb` outside every written range is zero
  have Z0 : ∀ a, a < Hb → (a < Z ∨ Z + m ≤ a) → (a < Z + M₀ ∨ Z + M₀ + m ≤ a) →
      (a < Z + 2 * M₀ ∨ Z + 2 * M₀ + m ≤ a) → (a < I0₀ ∨ I0₀ + L₀ ≤ a) →
      (a < I0₁ ∨ I0₁ + L₁ ≤ a) → (a < Y + 16 * S ∨ Y + 16 * S + 2 * w ≤ a) →
      (a < W' + 1 + (Z + 3 * M₀) ∨ W' + 1 + (Z + 3 * M₀) + m ≤ a) →
      (a < W' + 1 + (Z + 4 * M₀) ∨ W' + 1 + (Z + 4 * M₀) + w ≤ a) →
      (a < W' + 1 + (Z + 5 * M₀) ∨ W' + 1 + (Z + 5 * M₀) + w ≤ a) → mem a = 0 := by
    intro a ha k1 k2 k3 k4 k5 k6 k7 k8 k9
    by_cases hs : a ≤ sp
    · exact hz0 a hs
    · rw [hF a (by omega) k1 k2 k3 k4 k5 k6 k7 k8 k9 (Or.inl (by omega))]
      exact hc0 a (by omega) ha
  -- every cell `≤ W'` is a written word `≤ W'` or zero
  have LW : ∀ a ≤ W', mem a ≤ W' := by
    intro a ha
    by_cases r1 : Z ≤ a ∧ a < Z + m
    · have := vT (a - Z) (by omega); rwa [Nat.add_sub_cancel' r1.1] at this
    by_cases r2 : Z + M₀ ≤ a ∧ a < Z + M₀ + m
    · have := vH (a - (Z + M₀)) (by omega); rwa [Nat.add_sub_cancel' r2.1] at this
    by_cases r3 : Z + 2 * M₀ ≤ a ∧ a < Z + 2 * M₀ + m
    · have := vS (a - (Z + 2 * M₀)) (by omega); rwa [Nat.add_sub_cancel' r3.1] at this
    by_cases r4 : I0₀ ≤ a ∧ a < I0₀ + L₀
    · have := vA0 (a - I0₀) (by omega); rwa [Nat.add_sub_cancel' r4.1] at this
    by_cases r5 : I0₁ ≤ a ∧ a < I0₁ + L₁
    · have := vA1 (a - I0₁) (by omega); rwa [Nat.add_sub_cancel' r5.1] at this
    by_cases r6 : Y + 16 * S ≤ a ∧ a < Y + 16 * S + 2 * w
    · have := vP (a - (Y + 16 * S)) (by omega); rwa [Nat.add_sub_cancel' r6.1] at this
    rw [Z0 a (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega)]
    exact Nat.zero_le _
  have hres : ∀ a ≤ W', mem (W' + 1 + a) < M ∧
      (mem (W' + 1 + a) ≤ B ∨ M ≤ mem (W' + 1 + a) + B) := by
    intro a ha
    by_cases r : (W' + 1 + (Z + 3 * M₀) ≤ W' + 1 + a ∧ W' + 1 + a < W' + 1 + (Z + 3 * M₀) + m) ∨
      (W' + 1 + (Z + 4 * M₀) ≤ W' + 1 + a ∧ W' + 1 + a < W' + 1 + (Z + 4 * M₀) + w) ∨
      (W' + 1 + (Z + 5 * M₀) ≤ W' + 1 + a ∧ W' + 1 + a < W' + 1 + (Z + 5 * M₀) + w)
    · exact vR _ r
    · rw [Z0 (W' + 1 + a) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega)]
      exact ⟨hM, Or.inl (Nat.zero_le _)⟩
  refine ⟨fun a ha => ?_, fun a ha k1 k2 => ?_, LW, fun a ha => ?_, hres⟩
  · by_cases hs : a ≤ sp
    · exact hz0 a hs
    · exact Z0 a (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega)
  · exact Z0 a (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega)
  · by_cases h1 : a ≤ W'
    · have := LW a h1; omega
    by_cases h2 : W' + 1 + (W' + 1) ≤ a + 1
    · rw [Z0 a (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega)]
      exact Nat.zero_le _
    · have := (hres (a - (W' + 1)) (by omega)).1
      rw [show W' + 1 + (a - (W' + 1)) = a by omega] at this
      omega

end NegSSSP

end PlanarFlow
