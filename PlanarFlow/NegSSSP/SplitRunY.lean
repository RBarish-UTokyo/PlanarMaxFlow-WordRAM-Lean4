module

public import PlanarFlow.NegSSSP.SplitRunX

/-!
# The split exporting the sizes of the piece map in registers

**`bigProg_spec''`**: the statement of `bigProg_spec'` (same program `bigProg`, same bound
`bigT k`) with, in addition, the sizes of the piece map `kmap N K` in the **final** registers:
`r960 = m'` (darts), `r961 = nV` (vertices), `r962 = nF` (faces), and the registers of the
walks `r800 = m'`, `r801 … r805 = Y + j m'` (`Y = B₀ + 28 k + 3`), `r807 = nV`, `r808 = nF`. The
side arrays (`StR`, the layout registers of `sdWalk_exec`) are computed from these on the machine.
The proof is that of `bigProg_spec'` with a longer final `refine`.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false

namespace PlanarFlow

namespace NegSSSP

open Finset Function Equiv WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

variable {P : Input} {W : ℕ}

section Big

open Orbit CombMap BKMNW PlanarSeparator PlanarSeparator.MillerProg PlanarSeparator.StDart

universe u v w

variable {D : Type u} {V : Type v} {F : Type w} [Fintype D] [DecidableEq D] [Fintype V]
  [DecidableEq V] [Fintype F] [DecidableEq F] {N : CombMap D V F}
variable {Pc : Finset D} {m k : ℕ} {δ : ℕ → D} {α σ : ℕ → ℕ}

set_option maxHeartbeats 16000000 in
open Classical in
/-- **The large-component case of the split on the machine.** From the plain encoding of the
piece `Pc` (`PEnc`: the reversal at `bα`, the rotation at `bσ`) and the flags at `bF` of the
darts of a component `K = pcomp N Pc x₀` of more than three quarters of the darts (as `compProg`
leaves them), with the layout registers of `spSetup`, `bigProg` ends within `bigT k` steps with
a cut `A₀` of `K` meeting `CutOK` (the darts marked `1` by the separator run), the side of every
dart `x < m` at `Ob + x` (`0` exactly on the first part of `cutPair Pc K A₀`), and the positions
on the face of both parts (`PosInst`, the hypothesis `hpos` of `cornerProg_face`, the sources
being the shared vertices of the cut) at `T₁ + 2 (nV + nF)` and `T₂ + 2 (nV + nF)`. -/
theorem bigProg_spec'' (hM : N.IsPlane) (hrot : N.RotTrans) (hface : N.FaceTrans)
    (hPr : Pc ⊆ reps N) (he : PEnc N Pc m k δ α σ) {x₀ : D} (hx₀ : x₀ ∈ Pc)
    {bα bσ bF B₀ : ℕ} (c₀ : Config)
    (hc : WordsBounded W c₀) (r10 : c₀.nreg 10 = 1) (r860 : c₀.nreg 860 = m)
    (r861 : c₀.nreg 861 = k) (r862 : c₀.nreg 862 = bα) (r863 : c₀.nreg 863 = bσ)
    (r865 : c₀.nreg 865 = bF) (r950 : c₀.nreg 950 = B₀)
    (r951 : c₀.nreg 951 = B₀ + 25 * k + 3) (r952 : c₀.nreg 952 = B₀ + 28 * k + 3)
    (r953 : c₀.nreg 953 = B₀ + 33 * k + 3) (r955 : c₀.nreg 955 = B₀ + 41 * k + 4)
    (r956 : c₀.nreg 956 = B₀ + 42 * k + 4) (r957 : c₀.nreg 957 = B₀ + 54 * k + 7)
    (hα : ∀ h < k, c₀.nmem (bα + h) = α h) (hσ : ∀ h < k, c₀.nmem (bσ + h) = σ h)
    (hF : ∀ x < m, (c₀.nmem (bF + x) ≠ 0 ↔ δ x ∈ pcomp N Pc x₀))
    (lα : bα + k ≤ B₀) (lσ : bσ + k ≤ B₀) (lF : bF + m ≤ B₀)
    (hB : aEnd10 (3 * k) (3 * k) ≤ B₀) (hW : B₀ + 66 * k + 35 ≤ W)
    (hlo : ∀ a ≤ B₀ + 25 * k + 2, c₀.nmem a ≤ B₀ + 25 * k + 2) :
    ∃ c' t, Exec P W bigProg c₀ c' t ∧ t ≤ bigT k ∧
      (∀ a, B₀ + 66 * k + 10 ≤ a → c'.nmem a = c₀.nmem a) ∧
      (∀ r, 972 ≤ r → c'.nreg r = c₀.nreg r) ∧
      ∃ A₀, CutOK N (pcomp N Pc x₀) A₀ ∧
        (∀ x < m, c'.nmem (B₀ + 41 * k + 4 + x) =
          if δ x ∈ (cutPair Pc (pcomp N Pc x₀) A₀).1 then 0 else 1) ∧
        ∃ (nV nF q : ℕ) (ν : V → ℕ), (∀ v, ν v < nV) ∧ nV + nF ≤ 2 * k ∧
          q ≤ 6 * Nat.sqrt (12 * (pcomp N Pc x₀).card) + 4 ∧
          PosInst N (cutPair Pc (pcomp N Pc x₀) A₀).1 (bdry N A₀ (pcomp N Pc x₀ \ A₀))
            (18 * (pcomp N Pc x₀).card) q c'.nmem (B₀ + 42 * k + 4 + 2 * (nV + nF)) ν ∧
          PosInst N (cutPair Pc (pcomp N Pc x₀) A₀).2 (bdry N A₀ (pcomp N Pc x₀ \ A₀))
            (18 * (pcomp N Pc x₀).card) q c'.nmem (B₀ + 54 * k + 7 + 2 * (nV + nF)) ν ∧
          ∃ (m' : ℕ) (cn : SDart (rcl N (pcomp N Pc x₀)) ≃ Fin m')
            (vn : SVert (kσ N (pcomp N Pc x₀)) (rcl N (pcomp N Pc x₀)) ≃ Fin nV)
            (fn : (kmap N (pcomp N Pc x₀)).Face ≃ Fin nF)
            (ψ : V → SVert (kσ N (pcomp N Pc x₀)) (rcl N (pcomp N Pc x₀)))
            (C : (kst N (pcomp N Pc x₀)).SCycle) (Z : Finset (kst N (pcomp N Pc x₀)).Face),
            m' ≤ k ∧ (∀ v, ν v = vn (ψ v)) ∧ q = C.k ∧
            (∀ x : SDart (rcl N (pcomp N Pc x₀)),
              ψ (N.tail x.1) = (kmap N (pcomp N Pc x₀)).vert x) ∧
            side N (pcomp N Pc x₀) Z = A₀ ∧ side N (pcomp N Pc x₀) Zᶜ = pcomp N Pc x₀ \ A₀ ∧
            (∀ δ, ((kst N (pcomp N Pc x₀)).face δ ∈ Z ↔
              (kst N (pcomp N Pc x₀)).face ((kst N (pcomp N Pc x₀)).α δ) ∈ Z) ↔ ¬ C.Mem δ) ∧
            (∀ δ, ((kst N (pcomp N Pc x₀)).face δ ∈ Zᶜ ↔
              (kst N (pcomp N Pc x₀)).face ((kst N (pcomp N Pc x₀)).α δ) ∈ Zᶜ) ↔ ¬ C.Mem δ) ∧
            (∀ b ∈ bdry N A₀ (pcomp N Pc x₀ \ A₀), Sum.inl (ψ b) ∈ C.verts) ∧
            Enc (kmap N (pcomp N Pc x₀)) cn vn fn c'.nmem (B₀ + 28 * k + 3)
              (B₀ + 28 * k + 3 + m') (B₀ + 28 * k + 3 + 2 * m') (B₀ + 28 * k + 3 + 3 * m')
              (B₀ + 28 * k + 3 + 4 * m') ∧
            (∀ x, (kst N (pcomp N Pc x₀)).face (old x) ∈ Z ↔ c'.nmem (B₀ + 22 * m' + cn x) = 1) ∧
            (∀ x, (kst N (pcomp N Pc x₀)).face (old x) ∈ Zᶜ ↔
              c'.nmem (B₀ + 22 * m' + cn x) = 0) ∧
            (∀ h < k, ∀ hm : δ h ∈ rcl N (pcomp N Pc x₀),
              c'.nmem (B₀ + 25 * k + 3 + h) = cn ⟨δ h, hm⟩) ∧
            (∀ x < m, (c'.nmem (B₀ + 33 * k + 3 + x) ≠ 0 ↔ δ x ∈ pcomp N Pc x₀)) ∧
            c'.nreg 960 = m' ∧ c'.nreg 961 = nV ∧ c'.nreg 962 = nF ∧
            c'.nreg 800 = m' ∧ c'.nreg 801 = B₀ + 28 * k + 3 ∧
            c'.nreg 802 = B₀ + 28 * k + 3 + m' ∧ c'.nreg 803 = B₀ + 28 * k + 3 + 2 * m' ∧
            c'.nreg 804 = B₀ + 28 * k + 3 + 3 * m' ∧ c'.nreg 805 = B₀ + 28 * k + 3 + 4 * m' ∧
            c'.nreg 807 = nV ∧ c'.nreg 808 = nF := by
  set K := pcomp N Pc x₀ with hKdef
  have hKP : K ⊆ Pc := pcomp_subset Pc x₀
  have hx₀K : x₀ ∈ K := self_mem_pcomp hx₀
  have hKr : K ⊆ reps N := hKP.trans hPr
  have hK0 : K.Nonempty := ⟨x₀, hx₀K⟩
  have hKc : DConn N K := pcomp_dconn
  have hmk := he.mle
  have hKm : K.card ≤ m := by rw [he.enumP.card]; exact card_le_card hKP
  -- the encoding of the piece map of `K`
  obtain ⟨c₁, t₁, e₁, ht₁, m', nV, nF, cn, vn, fn, hE₁, hfl₁, g390, g391, g392, g393, hm'k, hX₁,
      fm₁, fr₁, -, -, -⟩ :=
    encStage_exec (P := P) he (shareClosed_pcomp Pc x₀) c₀ hc r10 r860 r861 r862 r863 r950 r951
      r865 hα hσ hF lα lσ lF hW
  obtain ⟨hcm, hnn, hKm', hm2⟩ := enc_card (N := N) (K := K) cn vn fn
  have hm1 : 1 ≤ m' := by have := card_pos.2 hK0; omega
  have R1 : ∀ r, (r = 10 ∨ r = 860 ∨ r = 861 ∨ r = 865 ∨ (950 ≤ r ∧ r ≤ 957) ∨ 972 ≤ r) →
      c₁.nreg r = c₀.nreg r := fun r hr => fr₁ r (by omega)
  -- the copy of the encoding
  obtain ⟨c₂, t₂, e₂, ht₂, cp₂, fm₂, fr₂, -, -, -⟩ :=
    cpyStage_exec (P := P) (m' := m') (B₀ := B₀) (Y := B₀ + 28 * k + 3) c₁ e₁.wb_right g390
      ((R1 950 (by omega)).trans r950) ((R1 952 (by omega)).trans r952) (by spomega)
      (by spomega)
  have R2 : ∀ r, (r = 10 ∨ r = 860 ∨ r = 861 ∨ r = 865 ∨ (950 ≤ r ∧ r ≤ 957) ∨ 972 ≤ r) →
      c₂.nreg r = c₀.nreg r := fun r hr =>
    (fr₂ r (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega)).trans (R1 r hr)
  -- the copy of the flags
  obtain ⟨c₃, t₃, e₃, ht₃, cp₃, fm₃, fr₃, -, -, -⟩ :=
    cpfStage_exec (P := P) (m := m) (bF := bF) (Fh := B₀ + 33 * k + 3) c₂ e₂.wb_right
      ((R2 860 (by omega)).trans r860) ((R2 865 (by omega)).trans r865)
      ((R2 953 (by omega)).trans r953) (by spomega) (by spomega)
  have R3 : ∀ r, (r = 10 ∨ r = 860 ∨ r = 861 ∨ r = 865 ∨ (950 ≤ r ∧ r ≤ 957) ∨ 972 ≤ r) →
      c₃.nreg r = c₀.nreg r := fun r hr =>
    (fr₃ r (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega)).trans (R2 r hr)
  have q390 : c₃.nreg 390 = m' := by
    rw [fr₃ 390 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
      fr₂ 390 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega), g390]
  have q391 : c₃.nreg 391 = nV := by
    rw [fr₃ 391 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
      fr₂ 391 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega), g391]
  have q392 : c₃.nreg 392 = nF := by
    rw [fr₃ 392 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
      fr₂ 392 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega), g392]
  -- the registers `< 700` cleared
  obtain ⟨c₄, t₄, e₄, ht₄, h390, h391, h392, h393, hz₄, h960, h961, h962, fr₄, fm₄, -, -, -⟩ :=
    zeroStage_exec (P := P) c₃ e₃.wb_right
  rw [q390] at h390 h960; rw [q391] at h391 h961; rw [q392] at h392 h962
  rw [R3 950 (by omega), r950] at h393
  have R4 : ∀ r, (r = 860 ∨ r = 861 ∨ r = 865 ∨ (950 ≤ r ∧ r ≤ 957) ∨ 972 ≤ r) →
      c₄.nreg r = c₀.nreg r := fun r hr => (fr₄ r (by omega) (by omega) (by omega)
        (by omega)).trans (R3 r (by omega))
  -- the memory before the separator run
  have M4 : ∀ a, a < B₀ + 28 * k + 3 → c₄.nmem a = c₁.nmem a := fun a ha => by
    rw [fm₄, fm₃ a (by omega), fm₂ a (by omega)]
  have MY4 : ∀ i < 5 * m', c₄.nmem (B₀ + 28 * k + 3 + i) = c₁.nmem (B₀ + i) := fun i hi => by
    rw [fm₄, fm₃ _ (by spomega), cp₂ i hi]
  have MF4 : ∀ x < m, c₄.nmem (B₀ + 33 * k + 3 + x) = c₀.nmem (bF + x) := fun x hx => by
    rw [fm₄, cp₃ x hx, fm₂ _ (by spomega), fm₁ _ (by spomega)]
  have MX4 : ∀ h < k, ∀ hm : δ h ∈ rcl N K, c₄.nmem (B₀ + 25 * k + 3 + h) = cn ⟨δ h, hm⟩ :=
    fun h hh hm => by rw [M4 _ (by spomega)]; exact hX₁ h hh hm
  -- the separator run
  obtain ⟨ψ, hψ⟩ := exists_kψ hrot hK0
  have hE₄ : Enc (kmap N K) cn vn fn c₄.nmem B₀ (B₀ + m') (B₀ + 2 * m') (B₀ + 3 * m')
      (B₀ + 4 * m') := enc_congr hE₁ fun i hi =>
    ⟨M4 _ (by spomega), M4 _ (by spomega), M4 _ (by spomega), M4 _ (by spomega),
      M4 _ (by spomega)⟩
  have hfl₄ : ∀ x, c₄.nmem (B₀ + 5 * m' + cn x) = flK N K x := fun x => by
    rw [M4 _ (by have := (cn x).2; spomega)]; exact hfl₁ x
  have hval := enc_vals hE₁ hfl₁
  obtain ⟨c₅, t₅, e₅, ht₅, F5r, F5m, hcut, C, Z, hside, z1, z2, hb1, hb2, hbs, hu, hdj, hck, -, -,
      -⟩ :=
    sep_run_lift (P := P) (W := W) (W₁ := B₀ + 25 * k + 2) hM hrot hface hKr hK0 hKc hψ cn vn fn
      hm1 hE₄ hfl₄ ((aEnd10_mono (by omega) (by omega)).trans hB) (by spomega) (by spomega)
      e₄.wb_right (fun r hr => by
        rcases (show r < 390 ∨ 393 < r ∨ r = 390 ∨ r = 391 ∨ r = 392 ∨ r = 393 by omega) with
          h | h | rfl | rfl | rfl | rfl
        · rw [hz₄ r hr (Or.inl h)]; omega
        · rw [hz₄ r hr (Or.inr h)]; omega
        · rw [h390]; spomega
        · rw [h391]; spomega
        · rw [h392]; spomega
        · rw [h393]; spomega)
      (fun a ha => by
        rw [M4 a (by spomega)]
        by_cases h1 : a < B₀
        · rw [fm₁ a (Or.inl h1)]; exact hlo a ha
        by_cases h2 : a < B₀ + 6 * m'
        · have := hval a (by omega) h2; generalize c₁.nmem a = z at this ⊢; spomega
        · rw [fm₁ a (Or.inr (Or.inl ⟨by omega, by spomega⟩))]; exact hlo a ha)
      h390 h391 h392 h393
  set A₀ := markSet N K cn (fun i => c₅.nmem (B₀ + 22 * m' + i)) with hA₀def
  have hA₀K : A₀ ⊆ K := fun d hd => (mem_markSet.1 hd).1
  have R5 : ∀ r, (r = 860 ∨ r = 861 ∨ r = 865 ∨ (950 ≤ r ∧ r ≤ 962) ∨ 972 ≤ r) →
      c₅.nreg r = c₄.nreg r := fun r hr => F5r r (by omega)
  -- the join of the sides
  obtain ⟨c₆, t₆, e₆, ht₆, j10, j780, j781, j782, j783, j792, fr₆, fm₆, -, -, -⟩ :=
    joinSet_exec (P := P) (B₀ := B₀) (m' := m') c₅ e₅.wb_right
      ((R5 950 (by omega)).trans ((R4 950 (by omega)).trans r950))
      ((R5 960 (by omega)).trans h960) (by spomega)
  rw [R5 860 (by omega), R4 860 (by omega), r860] at j780
  rw [R5 953 (by omega), R4 953 (by omega), r953] at j781
  rw [R5 951 (by omega), R4 951 (by omega), r951] at j782
  rw [R5 955 (by omega), R4 955 (by omega), r955] at j783
  have R6 : ∀ r, (r = 860 ∨ r = 861 ∨ r = 865 ∨ (950 ≤ r ∧ r ≤ 962) ∨ 972 ≤ r) →
      c₆.nreg r = c₄.nreg r := fun r hr =>
    (fr₆ r (by omega) (by omega) (by omega) (by omega) (by omega)).trans (R5 r hr)
  have MF6 : ∀ x < m, c₆.nmem (B₀ + 33 * k + 3 + x) = c₀.nmem (bF + x) := fun x hx => by
    rw [fm₆, F5m _ (by spomega), MF4 x hx]
  have MX6 : ∀ h < k, ∀ hm : δ h ∈ rcl N K, c₆.nmem (B₀ + 25 * k + 3 + h) = cn ⟨δ h, hm⟩ :=
    fun h hh hm => by rw [fm₆, F5m _ (by spomega)]; exact MX4 h hh hm
  have hKf : ∀ x < m, (c₆.nmem (B₀ + 33 * k + 3 + x) ≠ 0 ↔ δ x ∈ K) := fun x hx => by
    rw [MF6 x hx]; exact hF x hx
  have hidx : ∀ x < m, δ x ∈ K → c₆.nmem (B₀ + 25 * k + 3 + x) < m' := fun x hx hK => by
    rw [MX6 x (by omega) (subset_rcl K hK)]; exact (cn _).2
  obtain ⟨c₇, t₇, e₇, ht₇, hsd, fm₇, jfr⟩ :=
    joinProg_exec (P := P) (m := m) (Kb := B₀ + 33 * k + 3) (Ib := B₀ + 25 * k + 3)
      (Ob := B₀ + 41 * k + 4) (Zb := B₀ + 22 * m') c₆ e₆.wb_right
      ⟨by spomega, by spomega, fun x hx hf => by
          have := hidx x hx ((hKf x hx).1 hf)
          generalize c₆.nmem (B₀ + 25 * k + 3 + x) = z at this ⊢; left; spomega,
        fun x hx hf => by
          have := hidx x hx ((hKf x hx).1 hf)
          generalize c₆.nmem (B₀ + 25 * k + 3 + x) = z at this ⊢; spomega,
        by spomega, by spomega, by spomega, by spomega⟩
      ⟨j10, j780, j781, j782, j783, j792⟩
  have hsides : ∀ x < m, c₇.nmem (B₀ + 41 * k + 4 + x) =
      if δ x ∈ (cutPair Pc K A₀).1 then 0 else 1 := fun x hx => by
    rw [hsd x hx]
    refine joinProg_cutPair he.enumP hKP hA₀K hKf (fun y hy hyK => ?_) x hx
    rw [MX6 y (by omega) (subset_rcl K hyK), fm₆, hA₀def, mem_markSet]
    exact ⟨fun ⟨_, _, h1⟩ => h1, fun h1 => ⟨hyK, subset_rcl K hyK, h1⟩⟩
  have R7 : ∀ r, (r = 860 ∨ r = 861 ∨ r = 865 ∨ (950 ≤ r ∧ r ≤ 962) ∨ 972 ≤ r) →
      c₇.nreg r = c₄.nreg r := fun r hr => (jfr.nreg r (by omega)).trans (R6 r hr)
  -- the walk of the first side
  obtain ⟨c₈, t₈, e₈, ht₈, w800, w801, w802, w803, w804, w805, w806, w807, w808, w809, w810, fr₈,
      fm₈, -, -, -⟩ :=
    fw1Set_exec (P := P) (Y := B₀ + 28 * k + 3) (m' := m') c₇ e₇.wb_right
      ((R7 952 (by omega)).trans ((R4 952 (by omega)).trans r952))
      ((R7 960 (by omega)).trans h960) (by spomega)
  rw [jfr.nreg 792 (by omega), j792] at w806
  rw [R7 961 (by omega), h961] at w807
  rw [R7 962 (by omega), h962] at w808
  rw [R7 956 (by omega), R4 956 (by omega), r956] at w810
  have w10 : c₈.nreg 10 = 1 := by rw [fr₈ 10 (by omega), jfr.nreg 10 (by omega), j10]
  have MY8 : ∀ i < 5 * m', c₈.nmem (B₀ + 28 * k + 3 + i) = c₁.nmem (B₀ + i) := fun i hi => by
    rw [fm₈, fm₇ _ (Or.inl (by spomega)), fm₆, F5m _ (by spomega), MY4 i hi]
  have hE₈ : Enc (kmap N K) cn vn fn c₈.nmem (B₀ + 28 * k + 3) (B₀ + 28 * k + 3 + m')
      (B₀ + 28 * k + 3 + 2 * m') (B₀ + 28 * k + 3 + 3 * m') (B₀ + 28 * k + 3 + 4 * m') :=
    enc_congr hE₁ fun i hi =>
      ⟨MY8 i (by omega), by rw [Nat.add_assoc, MY8 _ (by omega), ← Nat.add_assoc],
        by rw [Nat.add_assoc, MY8 _ (by omega), ← Nat.add_assoc],
        by rw [Nat.add_assoc, MY8 _ (by omega), ← Nat.add_assoc],
        by rw [Nat.add_assoc, MY8 _ (by omega), ← Nat.add_assoc]⟩
  have hz₈ : ∀ x, (kst N K).face (old x) ∈ Z ↔ c₈.nmem (B₀ + 22 * m' + cn x) = 1 := fun x => by
    rw [fm₈, fm₇ _ (Or.inl (by have := (cn x).2; spomega)), fm₆]; exact z1 x
  set R₁ : Finset D := if A₀.card ≤ (K \ A₀).card then Pc \ K else ∅ with hR₁def
  set R₂ : Finset D := if A₀.card ≤ (K \ A₀).card then ∅ else Pc \ K with hR₂def
  have hv0 : verts N (∅ : Finset D) = ∅ := by simp [verts]
  have hR₁ : Disjoint (verts N R₁) (verts N K) := by
    rw [hR₁def]; split_ifs
    · exact disjoint_verts_pcomp Pc x₀
    · rw [hv0]; exact disjoint_empty_left _
  have hR₂ : Disjoint (verts N R₂) (verts N K) := by
    rw [hR₂def]; split_ifs
    · rw [hv0]; exact disjoint_empty_left _
    · exact disjoint_verts_pcomp Pc x₀
  obtain ⟨c₉, t₉, e₉, ht₉, sf₉, fm₉, pos₁⟩ :=
    faceWalk_pos (P := P) hM hrot hface hKr hK0 hKc hψ hb1
      (Bs := bdry N (side N K Z) (side N K Zᶜ)) (fun b hb => ⟨(hbs b hb).1, (hbs b hb).2.2⟩)
      hR₁ cn vn fn (Y := B₀ + 28 * k + 3) (bz := B₀ + 22 * m') (sv := 1)
      (T₀ := B₀ + 42 * k + 4) hE₈ hz₈ (by spomega) (by spomega) (by spomega) e₈.wb_right w10
      w800 w801 w802 w803 w804 w805 w806 w807 w808 w809 w810
  -- the walk of the second side
  obtain ⟨c₁₀, t₁₀, e₁₀, ht₁₀, v809, v810, fr₁₀, fm₁₀, -, -, -⟩ :=
    fw2Set_exec (P := P) c₉ e₉.wb_right
  rw [sf₉.nreg 957 (by omega), fr₈ 957 (by omega), R7 957 (by omega), R4 957 (by omega),
    r957] at v810
  have v8 : ∀ r, 800 ≤ r → r ≤ 808 → c₁₀.nreg r = c₈.nreg r := fun r h1 h2 => by
    rw [fr₁₀ r (by omega) (by omega), sf₉.nreg r (by omega)]
  have v10 : c₁₀.nreg 10 = 1 := by
    rw [fr₁₀ 10 (by omega) (by omega), sf₉.nreg 10 (by omega), w10]
  have MY10 : ∀ i < 5 * m', c₁₀.nmem (B₀ + 28 * k + 3 + i) = c₈.nmem (B₀ + 28 * k + 3 + i) :=
    fun i hi => by rw [fm₁₀, fm₉ _ (Or.inl (by spomega))]
  have hE₁₀ : Enc (kmap N K) cn vn fn c₁₀.nmem (B₀ + 28 * k + 3) (B₀ + 28 * k + 3 + m')
      (B₀ + 28 * k + 3 + 2 * m') (B₀ + 28 * k + 3 + 3 * m') (B₀ + 28 * k + 3 + 4 * m') :=
    enc_congr hE₈ fun i hi =>
      ⟨MY10 i (by omega), by rw [Nat.add_assoc, MY10 _ (by omega), ← Nat.add_assoc],
        by rw [Nat.add_assoc, MY10 _ (by omega), ← Nat.add_assoc],
        by rw [Nat.add_assoc, MY10 _ (by omega), ← Nat.add_assoc],
        by rw [Nat.add_assoc, MY10 _ (by omega), ← Nat.add_assoc]⟩
  have hz₁₀ : ∀ x, (kst N K).face (old x) ∈ Zᶜ ↔ c₁₀.nmem (B₀ + 22 * m' + cn x) = 0 :=
    fun x => by
      have := (cn x).2
      rw [fm₁₀, fm₉ _ (Or.inl (by spomega)), fm₈, fm₇ _ (Or.inl (by spomega)), fm₆]; exact z2 x
  obtain ⟨c₁₁, t₁₁, e₁₁, ht₁₁, sf₁₁, fm₁₁, pos₂⟩ :=
    faceWalk_pos (P := P) hM hrot hface hKr hK0 hKc hψ hb2
      (Bs := bdry N (side N K Z) (side N K Zᶜ)) (fun b hb => ⟨(hbs b hb).2.1, (hbs b hb).2.2⟩)
      hR₂ cn vn fn (Y := B₀ + 28 * k + 3) (bz := B₀ + 22 * m') (sv := 0)
      (T₀ := B₀ + 54 * k + 7) hE₁₀ hz₁₀ (by spomega) (by spomega) (by spomega) e₁₀.wb_right v10
      ((v8 800 (by omega) (by omega)).trans w800) ((v8 801 (by omega) (by omega)).trans w801)
      ((v8 802 (by omega) (by omega)).trans w802) ((v8 803 (by omega) (by omega)).trans w803)
      ((v8 804 (by omega) (by omega)).trans w804) ((v8 805 (by omega) (by omega)).trans w805)
      ((v8 806 (by omega) (by omega)).trans w806) ((v8 807 (by omega) (by omega)).trans w807)
      ((v8 808 (by omega) (by omega)).trans w808) v809 v810
  -- the parts
  have hsZ : side N K Z = A₀ := hside
  have hsZc : side N K Zᶜ = K \ A₀ := by rw [← hsZ]; exact eq_sdiff_of_union hu hdj
  rw [hsZ, hsZc] at pos₁ pos₂
  have hX1 : A₀ ∪ R₁ = (cutPair Pc K A₀).1 := by
    rw [hR₁def]; unfold cutPair; split_ifs <;> simp
  have hX2 : (K \ A₀) ∪ R₂ = (cutPair Pc K A₀).2 := by
    rw [hR₂def]; unfold cutPair; split_ifs <;> simp
  -- the time bound
  have hS : (1746 * K.card + 156) * (Nat.log 2 K.card + 3) ≤ (1746 * k + 156) * (Nat.log 2 k + 3) :=
    Nat.mul_le_mul (by omega)
      (by have := Nat.log_mono_right (b := 2) (show K.card ≤ k by omega); omega)
  have hsq : Nat.sqrt (12 * K.card) ≤ Nat.sqrt (12 * k) := Nat.sqrt_le_sqrt (by omega)
  refine ⟨c₁₁, t₁ + (t₂ + (t₃ + (t₄ + (t₅ + ((t₆ + t₇) + ((t₈ + t₉) + (t₁₀ + t₁₁))))))),
    .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ (.seq e₅ (.seq (.seq e₆ e₇) (.seq (.seq e₈ e₉)
      (.seq e₁₀ e₁₁))))))), ?_, fun a ha => ?_, fun r hr => ?_, A₀, hcut, fun x hx => ?_, nV, nF,
    C.k, fun v => vn (ψ v), fun v => (vn _).2, by spomega, hck,
    PosInst.congr pos₁ hX1 fun b _ => ?_, PosInst.congr pos₂ hX2 fun b _ => rfl,
    m', cn, vn, fn, ψ, C, Z, by spomega, fun v => rfl, rfl, hψ, hsZ, hsZc, hb1, hb2,
    fun b hb => (hbs b (by rw [hsZ, hsZc]; exact hb)).2.2, ?_, fun x => ?_, fun x => ?_,
    fun h hh hm => ?_, fun x hx => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold bigT
    clear * - ht₁ ht₂ ht₃ ht₄ ht₅ ht₆ ht₇ ht₈ ht₉ ht₁₀ ht₁₁ hck hS hsq hm'k hKm hmk
    generalize (1746 * K.card + 156) * (Nat.log 2 K.card + 3) = S₁ at ht₅ hS
    generalize (1746 * k + 156) * (Nat.log 2 k + 3) = S₂ at hS ⊢
    omega
  · rw [fm₁₁ a (Or.inr (by spomega)), fm₁₀, fm₉ a (Or.inr (by spomega)), fm₈,
      fm₇ a (Or.inr (by spomega)), fm₆, F5m a (by spomega), fm₄, fm₃ a (Or.inr (by spomega)),
      fm₂ a (Or.inr (by spomega)), fm₁ a (Or.inr (Or.inr (by spomega)))]
  · rw [sf₁₁.nreg r (by omega), fr₁₀ r (by omega) (by omega), sf₉.nreg r (by omega),
      fr₈ r (by omega), jfr.nreg r (by omega), R6 r (by omega), R4 r (by omega)]
  · rw [fm₁₁ _ (Or.inl (by spomega)), fm₁₀, fm₉ _ (Or.inl (by spomega)), fm₈]
    exact hsides x hx
  · have := (vn (ψ b)).2
    rw [fm₁₁ _ (Or.inl (by spomega)), fm₁₀]
  · exact enc_congr hE₁₀ fun i hi => by
      refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> exact fm₁₁ _ (Or.inl (by spomega))
  · have := (cn x).2
    rw [fm₁₁ _ (Or.inl (by spomega)), fm₁₀, fm₉ _ (Or.inl (by spomega))]; exact hz₈ x
  · have := (cn x).2
    rw [fm₁₁ _ (Or.inl (by spomega))]; exact hz₁₀ x
  · rw [fm₁₁ _ (Or.inl (by spomega)), fm₁₀, fm₉ _ (Or.inl (by spomega)), fm₈,
      fm₇ _ (Or.inl (by spomega))]
    exact MX6 h hh hm
  · rw [fm₁₁ _ (Or.inl (by spomega)), fm₁₀, fm₉ _ (Or.inl (by spomega)), fm₈,
      fm₇ _ (Or.inl (by spomega))]
    exact hKf x hx
  all_goals try (rw [sf₁₁.nreg _ (by omega), fr₁₀ _ (by omega) (by omega), sf₉.nreg _ (by omega),
    fr₈ _ (by omega), jfr.nreg _ (by omega), R6 _ (by omega)])
  · exact h960
  · exact h961
  · exact h962
  all_goals try (rw [sf₁₁.nreg _ (by omega), fr₁₀ _ (by omega) (by omega),
    sf₉.nreg _ (by omega)])
  · exact w800
  · exact w801
  · exact w802
  · exact w803
  · exact w804
  · exact w805
  · exact w807
  · exact w808


end Big

end NegSSSP

end PlanarFlow
