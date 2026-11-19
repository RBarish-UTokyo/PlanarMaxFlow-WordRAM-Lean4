module

public import PlanarFlow.BKMNW.LgS5B

/-!
# The large-piece separator, stage 5: the body (a nonempty piece map of the core)

* `s5ex` (the weights `pcExf + lmoved` of `pcertD` for the headline's choice `pcChoiceE`),
  `s5sc` (the headline's certificate choice `scChoiceE (sepC … (encB' W))`);
* `sum_enumG`, `inj_of_gidMono`;
* `s5BFr` (the registers kept by the body);
* **`s5Body_exec`**: `s5K ; lgKey ; s5C ; lgWt ; s5D ; ebProg ; s5E ; tfProg ; scProg mbBase`
  after `s5Pre`, for a nonempty piece map of the core `B` with a valid rotation (`CInvS`):
  within `9500 n + 40 k + 5 log₂ (2 W₀) + mbT n' (encB' W₀) W₀ + 3500` steps, the outcome of the
  certificate **of the headline** (`scertD (s5sc …) Hs B st (s5ex …)`, the certificate inside
  `pcertD (pcChoiceE …) (s5sc …) Q P Hs K st`), with the items at `ITEMb` and the path at `NHb`
  on the local enumeration `g ∘ IX`; memory below `b = U + 4n` kept.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false
set_option linter.tacticAnalysis.rwaSuggestion false

namespace PlanarFlow

namespace BKMNW

namespace MfDrv

open Finset Function Equiv WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs
  NegSSSP.Driver

universe w

variable {D : Type w} {V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}

variable (M) in
/-- **The weights of the certificate of a piece** for the headline's choice `pcChoiceE`. -/
noncomputable def s5ex (Q : Finset V) (eG : ℕ → D) (N : ℕ) (d₀ : D) (P : Finset D)
    (Hs : List (Finset V)) (K : ℕ) (d : D) : ℕ :=
  pcExf M (pcChoiceE M Q eG N d₀) Q P Hs K d +
    lmoved (pcExf M (pcChoiceE M Q eG N d₀) Q P Hs K) (pcLs M (pcChoiceE M Q eG N d₀) Q P Hs) d

variable (M) in
/-- **The headline's certificate choice** (`sc Hs A W` of `mfMain_cMachXGE`). -/
noncomputable def s5sc (eG : ℕ → D) (N : ℕ) (Hs : List (Finset V)) (A W : ℕ) : ScChoice M :=
  scChoiceE M (sepC M eG N (encB' W)) eG N Hs A W

/-- The registers kept by the body of stage 5. -/
def s5BFr (x : ℕ) : Prop := (700 ≤ x ∧ x < 3109) ∨ (3109 < x ∧ x < 4400) ∨ 7000 ≤ x

lemma inj_of_gidMono {gid : D → ℕ} {n : ℕ} {e : ℕ → D}
    (h : ∀ i j, i < j → j < n → gid (e i) < gid (e j)) :
    ∀ i < n, ∀ j < n, e i = e j → i = j := fun i hi j hj he => by
  rcases lt_trichotomy i j with hij | rfl | hij
  · have := h i j hij hj; rw [he] at this; omega
  · rfl
  · have := h j i hij hi; rw [he] at this; omega

lemma sum_enumG {B : Finset D} {n : ℕ} {e : ℕ → D} (hm : ∀ j < n, e j ∈ B)
    (hs : ∀ y ∈ B, ∃ j < n, e j = y) (hi : ∀ i < n, ∀ j < n, e i = e j → i = j) (f : D → ℕ) :
    ∑ j ∈ range n, f (e j) = ∑ d ∈ B, f d := by
  have hB : B = (range n).image e := by
    ext y
    simp only [mem_image, mem_range]
    constructor
    · intro hy; obtain ⟨j, hj, rfl⟩ := hs y hy; exact ⟨j, hj, rfl⟩
    · rintro ⟨j, hj, rfl⟩; exact hm j hj
  rw [hB, sum_image fun i hi' j hj' he => hi i (mem_range.1 hi') j (mem_range.1 hj') he]

section Exec

variable {I : Input} {W : ℕ}

/-- **Stage 5, the keys, the weights and the base**: `s5K ; lgKey ; s5C ; lgWt ; s5D ; ebProg`
after `s5Pre` (any `K` in `5910`, any `W₀` in `5912`). -/
theorem s5Mid_exec {gid : D → ℕ} {ν : V → ℕ} {S T Q : Finset V} {x : MCall M} {m n R : ℕ}
    {g : ℕ → D} (c : Config) (hc : WordsBounded W c)
    (hA : RArr M gid ν S T x m n R g c.nmem) (hTS : TailSorted M gid ν) (hQ : QPar Q ν)
    (hν : Injective ν) (hP : PcOK M S T x.1.piece x.2.1) (hHQ : Disjoint (hunion x.2.1) Q)
    (hQdeg : ∀ q ∈ Q, ∀ d d', M.tail d = q → M.tail d' = q → d = d')
    (hQ5 : ∀ d, ¬ (M.tail d ∈ Q ∧ M.head d ∈ Q)) {st : Perm D}
    {eG : ℕ → D} {N : ℕ} (he : ∀ i < N, gid (eG i) = i) (hesurj : ∀ d, ∃ i < N, eG i = d)
    (d₀ : D) {B : Finset D} (hB : B = pdarts M (core M Q x.1.piece) x.2.1) {n' U K W₀ : ℕ}
    (hn' : n' = B.card) (hne : 0 < n') (hS : S2Arr M gid c.nmem U n n' g B x.2.1 st)
    (r00 : c.nreg 5800 = n) (r01 : c.nreg 5801 = R + 3 + n) (r02 : c.nreg 5802 = R + 3 + 2 * n)
    (r03 : c.nreg 5803 = R + 3 + 4 * n) (r06 : c.nreg 5806 = 1) (r07 : c.nreg 5807 = 2)
    (r09 : c.nreg 5809 = U + 2 * n) (r10 : c.nreg 5810 = U + 4 * n)
    (r14 : c.nreg 5814 = U + 3 * n) (r70 : c.nreg 5870 = x.2.1.length)
    (r11 : c.nreg 5811 = n') (r910 : c.nreg 5910 = K) (r912 : c.nreg 5912 = W₀)
    (l0 : R + 3 + 6 * n + m ≤ U)
    (w : U + 600 * n + 6 * x.2.1.length + 2 * encB' W₀ + 20 * W₀ + K + 400 ≤ W) :
    ∃ c' t, Exec I W s5Mid c c' t ∧
      t ≤ 370 * n + 12 * x.2.1.length + 5 * Nat.log 2 (2 * W₀) + 300 ∧
      c'.nreg 5858 = encB' W₀ ∧
      (∀ y, (y < 4400 ∨ 7000 ≤ y ∨ y = 5800 ∨ y = 5810 ∨ y = 5811 ∨ y = 5814 ∨ y = 5911 ∨
        y = 5912) → c'.nreg y = c.nreg y) ∧
      (∀ a < U + 4 * n + 3 * n', c'.nmem a = c.nmem a) ∧
      (∀ i < n', c'.nmem (U + 4 * n + 6 * n' + i) < n') ∧
      (∀ i < n', ∀ j < n', (c'.nmem (U + 4 * n + 6 * n' + i) = c'.nmem (U + 4 * n + 6 * n' + j) ↔
        st.SameCycle (g (c.nmem (U + 2 * n + i))) (g (c.nmem (U + 2 * n + j))))) ∧
      (∀ j < n', c'.nmem (U + 4 * n + 3 * n' + j) =
        s5ex M Q eG N d₀ x.1.piece x.2.1 K (g (c.nmem (U + 2 * n + j)))) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hn'n : n' ≤ n := hS.le
  have he'inj : ∀ i < n', ∀ j < n', g (c.nmem (U + 2 * n + i)) = g (c.nmem (U + 2 * n + j)) →
      i = j := inj_of_gidMono hS.ixm
  -- `s5K`
  obtain ⟨c₁, t₁, e₁, ht₁, k21, f₁, m₁, rr₁, rm₁, o₁⟩ := s5K_exec (I := I) c hc (by omega)
  -- `lgKey`
  obtain ⟨c₂, t₂, e₂, ht₂, tk1, tk2, m₂, f₂, rr₂, rm₂, o₂⟩ := lgKey_exec (P := I)
    (e := fun j => g (c.nmem (U + 2 * n + j))) (τ := st) c₁ e₁.wb_right
    ((f₁ 5800 (by decide)).trans r00) ((f₁ 5810 (by decide)).trans r10)
    ((f₁ 5811 (by decide)).trans r11) ((f₁ 5814 (by decide)).trans r14) k21 hn'n
    (by omega) (by omega) (by omega) (fun j hj => by rw [m₁]; exact (hS.sg j hj).1)
    (fun j hj => by rw [m₁]; exact (hS.sg j hj).2) he'inj
  have q₂ : ∀ y, ¬ lgKw y → y ≠ 6521 → c₂.nreg y = c.nreg y := fun y h1 h2 => by
    rw [f₂ y h1, f₁ y h2]
  -- `s5C`
  obtain ⟨c₃, t₃, e₃, ht₃, s71, s72, s21, f₃, m₃, rr₃, rm₃, o₃⟩ := s5C_exec (I := I) c₂
    e₂.wb_right ((q₂ 5800 (by unfold lgKw; decide) (by decide)).trans r00)
    ((q₂ 5810 (by unfold lgKw; decide) (by decide)).trans r10)
    ((q₂ 5910 (by unfold lgKw; decide) (by decide)).trans r910) (by omega) (by omega)
  have q₃ : ∀ y, ¬ lgKw y → y ≠ 6521 → y ≠ 5871 → y ≠ 5872 → y ≠ 5943 → y ≠ 5946 →
      c₃.nreg y = c.nreg y := fun y h1 h2 h3 h4 h5 h6 => by rw [f₃ y h3 h4 h5 h6 h2, q₂ y h1 h2]
  have mem3 : ∀ a < U + 4 * n + 3 * n', c₃.nmem a = c.nmem a := fun a ha => by
    rw [m₃, m₂ a (by clear * - ha; omega) (by clear * - ha hn'n; omega), m₁]
  have hA₃ : RArr M gid ν S T x m n R g c₃.nmem := hA.congr fun a h1 h2 =>
    mem3 a (by clear * - h2 l0; omega)
  have hS₃ : S2Arr M gid c₃.nmem U n n' g B x.2.1 st := hS.congr fun a h1 h2 => mem3 a h2
  have hR₃ : WtR0 c₃ n (R + 3 + n) (R + 3 + 2 * n) (R + 3 + 4 * n) (U + 2 * n) (U + 4 * n) n'
      x.2.1.length K (U + 4 * n + 27 * n + 7) :=
    { r00 := (q₃ 5800 (by unfold lgKw; decide) (by decide) (by decide) (by decide) (by decide)
        (by decide)).trans r00
      r01 := (q₃ 5801 (by unfold lgKw; decide) (by decide) (by decide) (by decide) (by decide)
        (by decide)).trans r01
      r02 := (q₃ 5802 (by unfold lgKw; decide) (by decide) (by decide) (by decide) (by decide)
        (by decide)).trans r02
      r03 := (q₃ 5803 (by unfold lgKw; decide) (by decide) (by decide) (by decide) (by decide)
        (by decide)).trans r03
      r06 := (q₃ 5806 (by unfold lgKw; decide) (by decide) (by decide) (by decide) (by decide)
        (by decide)).trans r06
      r07 := (q₃ 5807 (by unfold lgKw; decide) (by decide) (by decide) (by decide) (by decide)
        (by decide)).trans r07
      r09 := (q₃ 5809 (by unfold lgKw; decide) (by decide) (by decide) (by decide) (by decide)
        (by decide)).trans r09
      r10 := (q₃ 5810 (by unfold lgKw; decide) (by decide) (by decide) (by decide) (by decide)
        (by decide)).trans r10
      r11 := (q₃ 5811 (by unfold lgKw; decide) (by decide) (by decide) (by decide) (by decide)
        (by decide)).trans r11
      r70 := (q₃ 5870 (by unfold lgKw; decide) (by decide) (by decide) (by decide) (by decide)
        (by decide)).trans r70
      r71 := s71, r72 := s72, r21 := s21 }
  -- `lgWt`
  obtain ⟨c₄, t₄, e₄, ht₄, hEX, m₄, f₄, rr₄, rm₄, o₄⟩ := lgWt_rec (P := I) c₃ e₃.wb_right hA₃ hTS
    hQ hν hP hHQ hQdeg hQ5 he hesurj d₀ hR₃ (hB ▸ hn') hne
    (fun j hj => hB ▸ hS₃.ix j hj) (fun y hy => hS₃.ixs y (hB ▸ hy)) hS₃.ixm hS₃.nf hS₃.th
    (by clear * - w; omega) (by clear * - w; omega) (by clear * - w; omega)
    (by clear * - l0; omega) (by clear * - hn'n; omega) (by clear * - hn'n; omega)
  have q₄ : ∀ y, ¬ lgKw y → y ≠ 6521 → y ≠ 5871 → y ≠ 5872 → y ≠ 5943 → y ≠ 5946 → ¬ wtW y →
      y ≠ 5804 → (y < 5873 ∨ 5889 < y) → y ≠ 5899 → c₄.nreg y = c.nreg y :=
    fun y h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 => by rw [f₄ y h7 h8 h9 h10, q₃ y h1 h2 h3 h4 h5 h6]
  -- `s5D ; ebProg`
  obtain ⟨c₅, t₅, e₅, ht₅, d50, f₅, m₅, rr₅, rm₅, o₅⟩ := s5D_exec (I := I) c₄ e₄.wb_right
  have r5 : c₅.nreg 5850 = W₀ := by
    rw [d50, q₄ 5912 (by unfold lgKw; decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by unfold wtW; decide) (by decide) (by decide) (by decide)]
    exact r912
  obtain ⟨c₆, t₆, e₆, ht₆, b58, f₆, m₆, rr₆, rm₆, o₆⟩ := ebProg_exec (P := I) c₅ e₅.wb_right r5
    (by clear * - w; omega) (by clear * - w; omega) (by clear * - w; omega)
  have q₆ : ∀ y, ¬ lgKw y → y ≠ 6521 → y ≠ 5871 → y ≠ 5872 → y ≠ 5943 → y ≠ 5946 → ¬ wtW y →
      y ≠ 5804 → (y < 5873 ∨ 5889 < y) → y ≠ 5899 → y ≠ 5850 → (y < 5851 ∨ 5859 < y) →
      c₆.nreg y = c.nreg y := fun y h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 => by
    rw [f₆ y h12, f₅ y h11, q₄ y h1 h2 h3 h4 h5 h6 h7 h8 h9 h10]
  have m64 : c₆.nmem = c₄.nmem := by rw [m₆, m₅]
  refine ⟨c₆, _, .seq (.seq e₁ e₂) (.seq (.seq e₃ e₄) (.seq e₅ e₆)), ?_, b58, fun y hy => ?_,
    fun a ha => ?_, fun i hi => ?_, fun i hi j hj => ?_, fun j hj => ?_, ?_, ?_, ?_⟩
  · clear * - ht₁ ht₂ ht₃ ht₄ ht₅ ht₆
    omega
  · exact q₆ y (by unfold lgKw; clear * - hy; omega) (by clear * - hy; omega)
      (by clear * - hy; omega) (by clear * - hy; omega) (by clear * - hy; omega)
      (by clear * - hy; omega) (by unfold wtW; clear * - hy; omega) (by clear * - hy; omega)
      (by clear * - hy; omega) (by clear * - hy; omega) (by clear * - hy; omega)
      (by clear * - hy; omega)
  · rw [m64, m₄ a (by clear * - ha hn'n; omega) (by clear * - ha; omega), mem3 a ha]
  · rw [m64, m₄ _ (by clear * - hi hn'n; omega) (by clear * - hi; omega), m₃]
    exact tk1 i hi
  · rw [m64, m₄ _ (by clear * - hi hn'n; omega) (by clear * - hi; omega), m₃,
      m₄ _ (by clear * - hj hn'n; omega) (by clear * - hj; omega), m₃]
    exact tk2 i hi j hj
  · have h1 := hEX j hj
    have h2 : c₃.nmem (U + 2 * n + j) = c.nmem (U + 2 * n + j) :=
      mem3 _ (by clear * - hj hn'n; omega)
    rw [h2] at h1
    rw [m64]; exact h1
  · rw [rr₆, rr₅, rr₄, rr₃, rr₂, rr₁]
  · rw [rm₆, rm₅, rm₄, rm₃, rm₂, rm₁]
  · rw [o₆, o₅, o₄, o₃, o₂, o₁]

end Exec

end MfDrv

end BKMNW

end PlanarFlow
