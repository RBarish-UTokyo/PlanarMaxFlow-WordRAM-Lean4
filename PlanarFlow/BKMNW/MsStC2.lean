module

public import PlanarFlow.BKMNW.MsStC

/-!
# The MSSP encoder, stage C1: the two Dijkstra runs on the cut

**`msC1`** `= cSetA ; msDk ; cSetB ; msDk`: Dijkstra's run (`msDk`) from the tail of the dart
whose word is at `GG = r8284` with the base `A0 = r8290`, then from the tail of the dart whose
word is at `IM + 12 nD + 1 + (1 mod k)` (the boundary dart `g (1 mod k)` of Klein's input,
`k = r8156`) with the base `A1 = r8291`. **`msC1_exec`**: both runs' distances, the tight
parents of the first run, the frame (memory changes only in the two Dijkstra areas).
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace PlanarFlow

namespace BKMNW

namespace MsEnc

open Finset Function WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs NsStep
  CombMap NegSSSP

variable {P : Input} {W : ℕ}

/-- The base and the root word of the first run. -/
def cSetA : Stmt := block [.copyN 8268 8290, .copyN 8267 8284]

/-- The base and the root word of the second run: `IM + 12 nD + 1 + (1 mod k)`. -/
def cSetB : Stmt :=
  block [.copyN 8268 8291, .constN 7360 12, .mulN 7361 7950 7360, .addN 7361 7361 8282,
    .constN 7360 1, .addN 7361 7361 7360, .modN 7362 7360 8156, .addN 8267 7361 7362]

/-- **Stage C1.** -/
def msC1 : Stmt := .seq cSetA (.seq msDk (.seq cSetB msDk))

theorem cSetA_exec (c : Config) (hc : WordsBounded W c) {A0 GG : ℕ} (r90 : c.nreg 8290 = A0)
    (r84 : c.nreg 8284 = GG) :
    ∃ c' t, Exec P W cSetA c c' t ∧ t = 2 ∧ c'.nreg 8268 = A0 ∧ c'.nreg 8267 = GG ∧
      (∀ r, r ≠ 8267 → r ≠ 8268 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold cSetA
  exec_block
  refine ⟨rfl, ?_, ?_, fun r a b => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals first
    | (simp only [r90, r84]; done)
    | (simp only [upd_apply]; split_ifs <;> first | omega | rfl)

theorem cSetB_exec (c : Config) (hc : WordsBounded W c) {A1 nD IM k : ℕ} (r91 : c.nreg 8291 = A1)
    (r50 : c.nreg 7950 = nD) (r82 : c.nreg 8282 = IM) (r56 : c.nreg 8156 = k) (hk : 0 < k)
    (hw : IM + 12 * nD + 1 + 1 ≤ W) (h12 : 12 ≤ W) :
    ∃ c' t, Exec P W cSetB c c' t ∧ t = 8 ∧ c'.nreg 8268 = A1 ∧
      c'.nreg 8267 = IM + 12 * nD + 1 + 1 % k ∧
      (∀ r, r ≠ 8267 → r ≠ 8268 → (r < 7360 ∨ 7362 < r) → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have h1k : 1 % k ≤ 1 := Nat.mod_le 1 k
  unfold cSetB
  exec_block
  all_goals try ((try config_simp); (try simp only [r91, r50, r82, r56]); omega)
  refine ⟨rfl, ?_, ?_, fun r a b d => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals first
    | (simp only [r91, r50, r82, r56]; done)
    | (simp only [upd_apply]; split_ifs <;> first | omega | rfl)
    | (simp only [r91, r50, r82, r56]; ring)

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F]

set_option maxHeartbeats 2000000 in
/-- **The two Dijkstra runs** (see the module docstring). -/
theorem msC1_exec {N : CombMap D V F} {nD cV : ℕ} (σ : D ≃ Fin nD) (τv : V ≃ Fin cV)
    {ιg : D → ℕ} {ιf : F → ℕ} {ιe : D → ℕ} {ℓD : D → ℤ} {IM LD A0 A1 H GG k : ℕ} {u₀ u₁ : V}
    (c : Config) (hc : WordsBounded W c)
    (hK : StEnc.KInM N σ (fun x => 1 + (τv x : ℕ)) ιg ιf ιe c.nmem IM)
    (hιe : ∀ d, ιe d < 4 * nD + 1)
    (hpos : ∀ d, 0 < ℓD d) (hLD : ∀ d, c.nmem (LD + σ d) = (ℓD d).toNat)
    (hL2 : ∀ d, (ℓD d).toNat ≤ H + H)
    (hreach : ∀ u x, MSSP.Reach (MSSP.pieceGraph N univ ℓD) u x)
    (hu₀ : c.nmem (IM + 4 * nD + c.nmem GG) = 1 + (τv u₀ : ℕ))
    (hu₁ : c.nmem (IM + 4 * nD + c.nmem (IM + 12 * nD + 1 + 1 % k)) = 1 + (τv u₁ : ℕ))
    (r50 : c.nreg 7950 = nD) (r82 : c.nreg 8282 = IM) (r88 : c.nreg 8288 = LD)
    (r90 : c.nreg 8290 = A0) (r91 : c.nreg 8291 = A1) (r35 : c.nreg 7335 = H)
    (r57 : c.nreg 7957 = cV) (r84 : c.nreg 8284 = GG) (r56 : c.nreg 8156 = k) (hk : 0 < k)
    (hcV : cV ≤ nD) (hGG : c.nmem GG < nD)
    (hG1 : c.nmem (IM + 12 * nD + 1 + 1 % k) < nD)
    (l1 : IM + 12 * nD + 1 + 2 ≤ A0) (l2 : LD + nD ≤ A0) (l3 : GG < A0)
    (l4 : A0 + 10 * (4 * nD + 1) + 1 + nD ≤ A1) (hW : A1 + 10 * (4 * nD + 1) + 1 + nD ≤ W)
    (hWI : cV * (H + H) + 1 + (H + H) ≤ W) (hGA : IM + 4 * nD + nD ≤ W) :
    ∃ e t, Exec P W msC1 c e t ∧ t ≤ 10 + 2 * (15 + stdCost (4 * nD + 1) nD) ∧
      (∀ x, e.nmem (A0 + 5 * (4 * nD + 1) + 1 + nD + (1 + (τv x : ℕ))) =
        (MSSP.dist (MSSP.pieceGraph N univ ℓD) u₀ x).toNat) ∧
      (∀ x, x ≠ u₀ → ∃ d, e.nmem (A0 + 9 * (4 * nD + 1) + 1 + nD + (1 + (τv x : ℕ))) = σ d ∧
        N.head d = x ∧ MSSP.dist (MSSP.pieceGraph N univ ℓD) u₀ (N.tail d) + ℓD d =
          MSSP.dist (MSSP.pieceGraph N univ ℓD) u₀ x) ∧
      (∀ x, e.nmem (A1 + 5 * (4 * nD + 1) + 1 + nD + (1 + (τv x : ℕ))) =
        (MSSP.dist (MSSP.pieceGraph N univ ℓD) u₁ x).toNat) ∧
      (∀ a, a < A0 ∨ A1 + 10 * (4 * nD + 1) + 1 + nD ≤ a → e.nmem a = c.nmem a) ∧
      (∀ r, (r < 1500 ∨ 2548 ≤ r) → (r < 7860 ∨ 7877 ≤ r) → (r < 7360 ∨ 7362 < r) →
        (r < 8264 ∨ 8268 < r) → e.nreg r = c.nreg r) ∧
      e.rreg = c.rreg ∧ e.rmem = c.rmem ∧ e.output = c.output := by
  have hσ : ∀ d, (σ d : ℕ) < nD := fun d => (σ d).2
  have hτ : ∀ x, (τv x : ℕ) < cV := fun x => (τv x).2
  obtain ⟨c₁, t₁, e₁, ht₁, a68, a67, aR, am, ar, arm, ao⟩ := cSetA_exec (P := P) c hc r90 r84
  have q1 : ∀ r, r ≠ 8267 → r ≠ 8268 → c₁.nreg r = c.nreg r := aR
  obtain ⟨c₂, t₂, e₂, ht₂, d0, p0, M₂, R₂, rr₂, rm₂, o₂⟩ :=
    msDk_exec (P := P) (N := N) σ τv (ℓD := ℓD) (IM := IM) (LD := LD) (Ab := A0) (H := H)
      (GA := GG) (u := u₀) c₁ e₁.wb_right (by rw [am]; exact hK) hpos
      (fun d => by rw [am]; exact hLD d) hL2 (hreach u₀) (by rw [am]; exact hu₀)
      (by rw [q1 _ (by omega) (by omega)]; exact r50) (by rw [q1 _ (by omega) (by omega)]; exact r82)
      (by rw [q1 _ (by omega) (by omega)]; exact r88) a68
      (by rw [q1 _ (by omega) (by omega)]; exact r35) (by rw [q1 _ (by omega) (by omega)]; exact r57)
      a67 hcV (by omega) l2 (by omega) hWI (by rw [am]; omega) (by omega)
  have q2 : ∀ r, (r < 1500 ∨ 2548 ≤ r) → (r < 7860 ∨ 7877 ≤ r) → (r < 8264 ∨ 8268 < r) →
      c₂.nreg r = c.nreg r := fun r h1 h2 h3 => by
    rw [R₂ r h1 h2 (by omega) (by omega) (by omega), q1 r (by omega) (by omega)]
  obtain ⟨c₃, t₃, e₃, ht₃, b68, b67, bR, bm, br, brm, bo⟩ :=
    cSetB_exec (P := P) c₂ e₂.wb_right (A1 := A1) (nD := nD) (IM := IM) (k := k)
      (by rw [q2 _ (by omega) (by omega) (by omega)]; exact r91)
      (by rw [q2 _ (by omega) (by omega) (by omega)]; exact r50)
      (by rw [q2 _ (by omega) (by omega) (by omega)]; exact r82)
      (by rw [q2 _ (by omega) (by omega) (by omega)]; exact r56) hk (by omega) (by omega)
  have m3 : ∀ a, a < A0 → c₃.nmem a = c.nmem a := fun a ha => by
    rw [bm, M₂ a (Or.inl ha), am]
  have q3 : ∀ r, (r < 1500 ∨ 2548 ≤ r) → (r < 7860 ∨ 7877 ≤ r) → (r < 7360 ∨ 7362 < r) →
      (r < 8264 ∨ 8268 < r) → c₃.nreg r = c.nreg r := fun r h1 h2 h3 h4 => by
    rw [bR r (by omega) (by omega) h3, q2 r h1 h2 h4]
  have h1k : 1 % k ≤ 1 := Nat.mod_le 1 k
  obtain ⟨c₄, t₄, e₄, ht₄, d1, -, M₄, R₄, rr₄, rm₄, o₄⟩ :=
    msDk_exec (P := P) (N := N) σ τv (ℓD := ℓD) (IM := IM) (LD := LD) (Ab := A1) (H := H)
      (GA := IM + 12 * nD + 1 + 1 % k) (u := u₁) c₃ e₃.wb_right
      (kInM_frame hK hιe (fun a h1 h2 => m3 a (by omega))) hpos
      (fun d => by rw [m3 _ (by have := hσ d; omega)]; exact hLD d) hL2 (hreach u₁)
      (by rw [m3 (IM + 12 * nD + 1 + 1 % k) (by omega),
        m3 _ (by have := hG1; omega)]; exact hu₁)
      (by rw [q3 _ (by omega) (by omega) (by omega) (by omega)]; exact r50)
      (by rw [q3 _ (by omega) (by omega) (by omega) (by omega)]; exact r82)
      (by rw [q3 _ (by omega) (by omega) (by omega) (by omega)]; exact r88) b68
      (by rw [q3 _ (by omega) (by omega) (by omega) (by omega)]; exact r35)
      (by rw [q3 _ (by omega) (by omega) (by omega) (by omega)]; exact r57)
      b67 hcV (by omega) (by omega) hW hWI
      (by rw [m3 _ (by omega)]; have := hG1; omega) (by omega)
  refine ⟨c₄, t₁ + (t₂ + (t₃ + t₄)), .seq e₁ (.seq e₂ (.seq e₃ e₄)), by omega,
    fun x => ?_, fun x hx => ?_, d1, fun a ha => ?_, fun r h1 h2 h3 h4 => ?_,
    by rw [rr₄, br, rr₂, ar], by rw [rm₄, brm, rm₂, arm], by rw [o₄, bo, o₂, ao]⟩
  · have := hτ x
    rw [M₄ _ (Or.inl (by omega)), bm]; exact d0 x
  · have := hτ x
    rw [M₄ _ (Or.inl (by omega)), bm]; exact p0 x hx
  · rw [M₄ a (by omega), bm, M₂ a (by omega), am]
  · rw [R₄ r h1 h2 (by omega) (by omega) (by omega), q3 r h1 h2 h3 h4]

end MsEnc

end BKMNW

end PlanarFlow
