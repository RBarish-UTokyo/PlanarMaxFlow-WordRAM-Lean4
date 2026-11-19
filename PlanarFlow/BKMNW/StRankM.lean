module

public import PlanarFlow.BKMNW.StRank
public import PlanarFlow.BKMNW.StMapG

/-!
# Compact node numbers for Klein's encoding of the dual of a piece map

`smP_lay` writes Klein's encoding `KInM Q σ ιv ιg ιf ιe` of `Q = (pmap hP).dual` with the orbit
labels `ιv = fLab + 1` (values in `[1, m]`) and `ιf = 2m + 1 + fLab` (values in `[2m+1, 3m]`),
injective but not onto. `cmProg` relabels the arrays `NT`, `NH` (by the ranks of the vertices of
`Q`) and `NF` (by the ranks of its faces):

* `rkRl s` (rank of one label array, relabel it in place, the count saved in `r s`),
  **`rkRl_exec`** (on a map: `τ : X ≃ Fin K`, the array becomes `of + τ (lab d)`, `R[ι x - of] =
  τ x`);
* **`cmProg`**, **`cmProg_kin`**: within `51 nD + 30 m + 45` steps the memory holds
  `KInM Q σ (1 + τv) ιg (2m + 1 + τf) ιe` for `τv : X ≃ Fin nV`, `τf : Y ≃ Fin nF`
  (`nV = r7957`, `nF = r7959`), the other words of the encoding kept;
* **`smLayoutC`**: the node layout `Klein.Layout M.dual n (1 + τv) (ιG …) (2m+1 + τf) (ιE …)` for
  any injective `τv`, `τf` below `m` (`4 m + 1 ≤ n`), the compact version of `smLayout`.

With the compact numbering, `NegSSSP.toProg_orders` and `NegSSSP.cotProg_exec` apply with
`of = 1`, `τ = τv` (the spanning tree of `Q.dual`, nodes the faces of the piece map) and
`of = 2m + 1`, `τ = τf` (the cotree, nodes the vertices).

Registers: natural `7950 … 7955` (inputs `nD`, `NTb`, `NHb`, `NFb`, `m`, `Rb`), `7957`, `7959`
(the counts), `7958` and the registers of `rkProg`, `rlProg` (`7920 … 7931`, `7940 … 7947`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace BKMNW

namespace StEnc

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs NegSSSP

/-- Rank one label array and relabel it, the count saved in `r s`. -/
def rkRl (s : ℕ) : Stmt :=
  .seq rkProg (.seq (block [.copyN s 7930, .copyN 7940 7920, .copyN 7941 7921, .copyN 7942 7922,
    .copyN 7943 7924]) rlProg)

/-- **Compact numbers in Klein's encoding**: rank and relabel `NT`, relabel `NH`, rank and
relabel `NF`. -/
def cmProg : Stmt :=
  .seq (block [.copyN 7920 7950, .copyN 7921 7951, .constN 7922 1, .copyN 7923 7954,
    .copyN 7924 7955]) <|
  .seq (rkRl 7957) <|
  .seq (block [.copyN 7941 7952]) <|
  .seq rlProg <|
  .seq (block [.copyN 7921 7953, .constN 7958 1, .addN 7922 7954 7954, .addN 7922 7922 7958])
    (rkRl 7959)

theorem cmProg_natOnly : Klein.natOnly cmProg = true := by kernel_rfl

variable {P : Input} {W : ℕ}

section Gen

variable {D' X : Type*} [Fintype D'] [DecidableEq D'] [Fintype X] [DecidableEq X]

/-- **Rank and relabel one label array on a map**: the array `A[σ d] = ι (lab d)` (`lab` onto,
`ι` injective into `[of, of + N)`) becomes `of + τ (lab d)` for a bijection `τ : X ≃ Fin K`,
`K` saved in `r s`, the ranks `R[ι x - of] = τ x` kept at `Rb`. -/
theorem rkRl_exec {nD : ℕ} (σ : D' ≃ Fin nD) {ι : X → ℕ} (hinj : Function.Injective ι)
    {lab : D' → X} (hlab : Function.Surjective lab) {Ab of N Rb s : ℕ}
    (hlo : ∀ x, of ≤ ι x) (hhi : ∀ x, ι x < of + N)
    (hs : s ≠ 7920 ∧ s ≠ 7921 ∧ s ≠ 7922 ∧ s ≠ 7923 ∧ s ≠ 7924 ∧ s ≠ 7930 ∧ s ≠ 7940 ∧
      s ≠ 7941 ∧ s ≠ 7942 ∧ s ≠ 7943 ∧ (s < 7926 ∨ 7931 < s) ∧ (s < 7944 ∨ 7947 < s))
    (hW : Rb + N ≤ W) (hAW : Ab + nD ≤ W) (hNW : of + N + 1 ≤ W)
    (hd : Ab + nD ≤ Rb ∨ Rb + N ≤ Ab) (c : Config) (hc : WordsBounded W c)
    (h20 : c.nreg 7920 = nD) (h21 : c.nreg 7921 = Ab) (h22 : c.nreg 7922 = of)
    (h23 : c.nreg 7923 = N) (h24 : c.nreg 7924 = Rb)
    (hA : ∀ d, c.nmem (Ab + σ d) = ι (lab d)) :
    ∃ c' t, Exec P W (rkRl s) c c' t ∧ t ≤ 18 * nD + 15 * N + 21 ∧ c'.nreg s ≤ N ∧
      ∃ τ : X ≃ Fin (c'.nreg s),
        (∀ d, c'.nmem (Ab + σ d) = of + τ (lab d)) ∧
        (∀ x, c'.nmem (Rb + (ι x - of)) = τ x) ∧
        (∀ a, (a < Ab ∨ Ab + nD ≤ a) → (a < Rb ∨ Rb + N ≤ a) → c'.nmem a = c.nmem a) ∧
        c'.nreg 7940 = nD ∧ c'.nreg 7942 = of ∧ c'.nreg 7943 = Rb ∧
        (∀ r, r ≠ s → (r < 7926 ∨ 7931 < r) → (r < 7940 ∨ 7947 < r) → c'.nreg r = c.nreg r) ∧
        c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨hs0, hs1, hs2, hs3, hs4, hs30, hs40, hs41, hs42, hs43, hsa, hsb⟩ := hs
  set A : ℕ → ℕ := fun i => if h : i < nD then ι (lab (σ.symm ⟨i, h⟩)) else 0 with hAdef
  have hAσ : ∀ d, A (σ d) = ι (lab d) := fun d => by
    simp only [hAdef, (σ d).2, ↓reduceDIte]; simp
  have hAi : ∀ i < nD, c.nmem (Ab + i) = A i := fun i hi => by
    have := hA (σ.symm ⟨i, hi⟩)
    rw [Equiv.apply_symm_apply] at this
    rw [this]; simp only [hAdef, hi, ↓reduceDIte]
  have hAlt : ∀ i < nD, A i - of < N := fun i hi => by
    simp only [hAdef, hi, ↓reduceDIte]
    have := hlo (lab (σ.symm ⟨i, hi⟩)); have := hhi (lab (σ.symm ⟨i, hi⟩)); omega
  obtain ⟨τ, hτ⟩ := rk_equiv hinj hlo hhi (A := A) (nA := nD)
    (fun i hi => ⟨lab (σ.symm ⟨i, hi⟩), by simp only [hAdef, hi, ↓reduceDIte]⟩)
    (fun x => by
      obtain ⟨d, rfl⟩ := hlab x
      exact ⟨σ d, (σ d).2, hAσ d⟩)
  obtain ⟨c₁, t₁, e₁, ht₁, k0, k1, k30, kR⟩ := rkProg_exec (P := P) (A := A) hW hAW (by omega) hd
    hAlt c hc h20 h21 h22 h23 h24 hAi
  have q : ∀ r, r < 7926 ∨ 7931 < r → c₁.nreg r = c.nreg r := kR.1
  have hR1 : ∀ x, c₁.nmem (Rb + (ι x - of)) = τ x := fun x => by
    have := hlo x; have := hhi x
    rw [k0 _ (by omega) (hτ x).2, (hτ x).1]
  have hA1 : ∀ i < nD, c₁.nmem (Ab + i) = A i := fun i hi => by
    rw [k1 _ (by omega)]; exact hAi i hi
  -- the copies
  have hw₁ := e₁.wb_right
  clear hc
  obtain ⟨c₂, t₂, e₂, ht₂, b30, b40, b41, b42, b43, bn, bm, br, brm, bo⟩ : ∃ c' t, Exec P W
      (block [.copyN s 7930, .copyN 7940 7920, .copyN 7941 7921, .copyN 7942 7922,
        .copyN 7943 7924]) c₁ c' t ∧ t = 5 ∧ c'.nreg s = c₁.nreg 7930 ∧ c'.nreg 7940 = nD ∧
      c'.nreg 7941 = Ab ∧ c'.nreg 7942 = of ∧ c'.nreg 7943 = Rb ∧
      (∀ r, r ≠ s → r ≠ 7940 → r ≠ 7941 → r ≠ 7942 → r ≠ 7943 → c'.nreg r = c₁.nreg r) ∧
      c'.nmem = c₁.nmem ∧ c'.rreg = c₁.rreg ∧ c'.rmem = c₁.rmem ∧ c'.output = c₁.output := by
    exec_block
    refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, fun r h1 h2 h3 h4 h5 => ?_, rfl, rfl, rfl, rfl⟩ <;>
      config_simp <;> simp only [upd_apply] <;> split_ifs <;>
      first | omega | rfl | (rw [q _ (by omega)]; assumption)
  have hτv : ∀ i < nD, of + c₂.nmem (Rb + (c₂.nmem (Ab + i) - of)) ≤ W := fun i hi => by
    rw [bm, hA1 i hi]
    have e := hAσ (σ.symm ⟨i, hi⟩)
    rw [Equiv.apply_symm_apply] at e
    simp only at e
    rw [e, hR1]
    have := (τ (lab (σ.symm ⟨i, hi⟩))).2
    have := rkC_le (mkF A of nD) N
    omega
  obtain ⟨c₃, t₃, e₃, ht₃, l0, l1, ln, lr, lrm, lo⟩ := rlProg_exec (P := P) (N := N) hW hAW
    (by omega) (by omega) c₂ e₂.wb_right b40 b41 b42 b43
    (fun i hi => by rw [bm, hA1 i hi]; exact hAlt i hi) hτv
  have e3s : c₃.nreg s = c₁.nreg 7930 := by rw [ln s (by omega), b30]
  have hK : rkC (mkF A of nD) N = c₃.nreg s := by rw [e3s, k30]
  have hm23 : ∀ a, (a < Ab ∨ Ab + nD ≤ a) → c₃.nmem a = c₁.nmem a := fun a ha => by
    rw [l1 a ha, bm]
  refine ⟨c₃, t₁ + (t₂ + t₃), Exec.seq e₁ (Exec.seq e₂ e₃), by omega,
    by rw [← hK]; exact rkC_le _ _, τ.trans (finCongr hK),
    fun d => ?_, fun x => ?_, fun a h1 h2 => ?_, by rw [ln _ (by omega)]; exact b40,
    by rw [ln _ (by omega)]; exact b42, by rw [ln _ (by omega)]; exact b43,
    fun r h1 h2 h3 => ?_, by rw [lr, br, kR.2.1], by rw [lrm, brm, kR.2.2.1],
    by rw [lo, bo, kR.2.2.2]⟩
  · simp only [Equiv.trans_apply, finCongr_apply, Fin.val_cast]
    rw [l0 _ (σ d).2, bm, hA1 _ (σ d).2, hAσ, hR1]
  · simp only [Equiv.trans_apply, finCongr_apply, Fin.val_cast]
    have := hlo x; have := hhi x
    rw [hm23 _ (by omega), hR1]
  · rw [hm23 a h1, k1 a h2]
  · rw [ln r (by omega), bn r h1 (by omega) (by omega) (by omega) (by omega), q r h2]

end Gen

section Map

variable {D' X Y : Type*} [Fintype D'] [DecidableEq D'] [Fintype X] [DecidableEq X] [Fintype Y]
  [DecidableEq Y]

/-- **Compact node numbers in Klein's encoding of a map** `Q` (in the memory at `β`): the vertex
nodes `ιv` (injective, in `[1, 1 + m)`) and the face nodes `ιf` (injective, in
`[2m+1, 3m+1)`) become `1 + τv` and `2m + 1 + τf` for bijections `τv : X ≃ Fin nV`,
`τf : Y ≃ Fin nF` (`nV = r7957`, `nF = r7959`); the other words of the encoding are kept, the
scratch is `[Rb, Rb + m)`. -/
theorem cmProg_kin {Q : CombMap D' X Y} {nD m : ℕ} (σ : D' ≃ Fin nD) {ιv : X → ℕ}
    {ιg : D' → ℕ} {ιf : Y → ℕ} {ιe : D' → ℕ} {β Rb E : ℕ} (c : Config) (hc : WordsBounded W c)
    (hK : KInM Q σ ιv ιg ιf ιe c.nmem β)
    (hvinj : Function.Injective ιv) (hvlo : ∀ x, 1 ≤ ιv x) (hvhi : ∀ x, ιv x < 1 + m)
    (hfinj : Function.Injective ιf) (hflo : ∀ y, 2 * m + 1 ≤ ιf y)
    (hfhi : ∀ y, ιf y < 2 * m + 1 + m)
    (htS : Function.Surjective Q.tail) (hfS : Function.Surjective Q.face)
    (hE : ∀ d, ιe d < E) (hRb : β + 8 * nD + E ≤ Rb) (hW : Rb + m ≤ W) (hmW : 3 * m + 2 ≤ W)
    (r50 : c.nreg 7950 = nD) (r51 : c.nreg 7951 = β + Klein.iNT nD)
    (r52 : c.nreg 7952 = β + Klein.iNH nD) (r53 : c.nreg 7953 = β + Klein.iNF nD)
    (r54 : c.nreg 7954 = m) (r55 : c.nreg 7955 = Rb) :
    ∃ c' t, Exec P W cmProg c c' t ∧ t ≤ 46 * nD + 30 * m + 56 ∧
      ∃ (τv : X ≃ Fin (c'.nreg 7957)) (τf : Y ≃ Fin (c'.nreg 7959)),
        KInM Q σ (fun x => 1 + τv x) ιg (fun y => 2 * m + 1 + τf y) ιe c'.nmem β ∧
        (∀ a, (a < β + nD ∨ β + 2 * nD ≤ a) → (a < β + 4 * nD ∨ β + 6 * nD ≤ a) →
          (a < Rb ∨ Rb + m ≤ a) → c'.nmem a = c.nmem a) ∧
        (∀ r, r < 7920 ∨ (7947 < r ∧ r < 7957) ∨ 7959 < r → c'.nreg r = c.nreg r) ∧
        c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold cmProg
  have hNT := hK.nt; have hNH := hK.nh; have hNF := hK.nf
  simp only [Klein.iNT, Klein.iNH, Klein.iNF] at r51 r52 r53 hNT hNH hNF
  -- setup
  obtain ⟨c₁, t₁, e₁, ht₁, a20, a21, a22, a23, a24, an, am, ar, arm, ao⟩ : ∃ c' t, Exec P W
      (block [.copyN 7920 7950, .copyN 7921 7951, .constN 7922 1, .copyN 7923 7954,
        .copyN 7924 7955]) c c' t ∧ t = 5 ∧ c'.nreg 7920 = nD ∧ c'.nreg 7921 = β + 4 * nD ∧
      c'.nreg 7922 = 1 ∧ c'.nreg 7923 = m ∧ c'.nreg 7924 = Rb ∧
      (∀ r, (r < 7920 ∨ 7924 < r) → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
    exec_block
    · omega
    refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩ <;>
      config_simp <;> (try simp only [upd_apply]) <;> (try split_ifs) <;>
      first | omega | rfl | assumption | (rw [r54]) | (rw [r55])
  -- rank and relabel `NT`
  obtain ⟨c₂, t₂, e₂, ht₂, bK, τ₁, b0, bR, bm, b40, b42, b43, bn, br, brm, bo⟩ :=
    rkRl_exec (P := P) (s := 7957) σ hvinj htS (Ab := β + 4 * nD) hvlo hvhi
      (by omega) hW (by omega) (by omega) (Or.inl (by omega)) c₁ e₁.wb_right a20 a21 a22 a23 a24
      (fun d => by rw [am]; exact hNT d)
  -- the reads of `NH`
  obtain ⟨c₃, t₃, e₃, ht₃, d41, dn, dm, dr, drm, do_⟩ : ∃ c' t, Exec P W
      (block [.copyN 7941 7952]) c₂ c' t ∧ t = 1 ∧ c'.nreg 7941 = β + 5 * nD ∧
      (∀ r, r ≠ 7941 → c'.nreg r = c₂.nreg r) ∧ c'.nmem = c₂.nmem ∧
      c'.rreg = c₂.rreg ∧ c'.rmem = c₂.rmem ∧ c'.output = c₂.output := by
    have hw₂ := e₂.wb_right
    clear hc
    exec_block
    refine ⟨rfl, ?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩ <;> config_simp
    · rw [bn _ (by omega) (by omega) (by omega), an _ (by omega)]; exact r52
    · simp only [upd_apply, hr, ↓reduceIte]
  have hNH2 : ∀ d, c₂.nmem (β + 5 * nD + σ d) = ιv (Q.head d) := fun d => by
    have := (σ d).2
    rw [bm _ (Or.inr (by omega)) (Or.inl (by omega)), am]; exact hNH d
  have hNHi : ∀ i (hi : i < nD), c₃.nmem (β + 5 * nD + i) = ιv (Q.head (σ.symm ⟨i, hi⟩)) :=
    fun i hi => by
      have := hNH2 (σ.symm ⟨i, hi⟩)
      rw [Equiv.apply_symm_apply] at this
      rw [dm]; exact this
  obtain ⟨c₄, t₄, e₄, ht₄, l0, l1, ln, lr, lrm, lo⟩ := rlProg_exec (P := P) (N := m) (nA := nD) (Xb := β + 5 * nD) (of := 1) (Rb := Rb) hW
    (by omega) (by omega) (Or.inl (by omega)) c₃ e₃.wb_right
    (by rw [dn _ (by omega)]; exact b40) d41 (by rw [dn _ (by omega)]; exact b42)
    (by rw [dn _ (by omega)]; exact b43)
    (fun i hi => by
      rw [hNHi i hi]
      have := hvlo (Q.head (σ.symm ⟨i, hi⟩)); have := hvhi (Q.head (σ.symm ⟨i, hi⟩)); omega)
    (fun i hi => by
      rw [hNHi i hi, dm, bR]
      have := (τ₁ (Q.head (σ.symm ⟨i, hi⟩))).2
      omega)
  -- the setup of the faces
  have r40₄ : c₄.nreg 7940 = nD := by rw [ln _ (by omega), dn _ (by omega)]; exact b40
  have fr : ∀ r, r < 7920 ∨ (7947 < r ∧ r < 7957) ∨ 7959 < r → c₄.nreg r = c.nreg r :=
    fun r hr => by
      rw [ln _ (by omega), dn _ (by omega), bn _ (by omega) (by omega) (by omega),
        an _ (by omega)]
  obtain ⟨c₅, t₅, e₅, ht₅, g21, g22, gn, gm, gr, grm, go⟩ : ∃ c' t, Exec P W
      (block [.copyN 7921 7953, .constN 7958 1, .addN 7922 7954 7954, .addN 7922 7922 7958])
      c₄ c' t ∧ t = 4 ∧ c'.nreg 7921 = β + nD ∧ c'.nreg 7922 = 2 * m + 1 ∧
      (∀ r, r ≠ 7921 → r ≠ 7922 → r ≠ 7958 → c'.nreg r = c₄.nreg r) ∧ c'.nmem = c₄.nmem ∧
      c'.rreg = c₄.rreg ∧ c'.rmem = c₄.rmem ∧ c'.output = c₄.output := by
    have hw₄ := e₄.wb_right
    have q53 : c₄.nreg 7953 = β + nD := (fr _ (by omega)).trans r53
    have q54 : c₄.nreg 7954 = m := (fr _ (by omega)).trans r54
    clear hc
    exec_block
    · omega
    · config_simp; rw [q54]; omega
    · config_simp; rw [q54]; omega
    refine ⟨rfl, ?_, ?_, fun r h1 h2 h3 => ?_, rfl, rfl, rfl, rfl⟩ <;> config_simp
    · exact q53
    · rw [q54]; omega
    · simp only [upd_apply, h1, h2, h3, ↓reduceIte]
  have q4 : ∀ r, r < 7926 ∨ (7931 < r ∧ r < 7940) ∨ 7947 < r → c₄.nreg r = c₂.nreg r :=
    fun r hr => by rw [ln _ (by omega), dn _ (by omega)]
  have hNF5 : ∀ d, c₅.nmem (β + nD + σ d) = ιf (Q.face d) := fun d => by
    have := (σ d).2
    rw [gm, l1 _ (Or.inl (by omega)), dm, bm _ (Or.inl (by omega)) (Or.inl (by omega)), am]
    exact hNF d
  obtain ⟨c₆, t₆, e₆, ht₆, hK6, τ₂, h0, hR6, hm6, -, -, -, hn6, hr6, hrm6, ho6⟩ :=
    rkRl_exec (P := P) (s := 7959) σ hfinj hfS (Ab := β + nD) hflo hfhi
      (by omega) hW (by omega) (by omega) (Or.inl (by omega)) c₅ e₅.wb_right
      (by rw [gn _ (by omega) (by omega) (by omega), q4 _ (by omega), bn _ (by omega) (by omega)
        (by omega)]; exact a20) g21 g22
      (by rw [gn _ (by omega) (by omega) (by omega), q4 _ (by omega), bn _ (by omega) (by omega)
        (by omega)]; exact a23)
      (by rw [gn _ (by omega) (by omega) (by omega), q4 _ (by omega), bn _ (by omega) (by omega)
        (by omega)]; exact a24) hNF5
  -- the memory
  have m6 : ∀ a, (a < β + nD ∨ β + 2 * nD ≤ a) → (a < Rb ∨ Rb + m ≤ a) →
      c₆.nmem a = c₄.nmem a := fun a h1 h2 => by rw [hm6 a (by omega) h2, gm]
  have m4 : ∀ a, (a < β + 5 * nD ∨ β + 6 * nD ≤ a) → c₄.nmem a = c₂.nmem a := fun a h => by
    rw [l1 a (by omega), dm]
  have m2 : ∀ a, (a < β + 4 * nD ∨ β + 5 * nD ≤ a) → (a < Rb ∨ Rb + m ≤ a) →
      c₂.nmem a = c.nmem a := fun a h1 h2 => by rw [bm a (by omega) h2, am]
  have mk : ∀ a, (a < β + nD ∨ β + 2 * nD ≤ a) → (a < β + 4 * nD ∨ β + 6 * nD ≤ a) →
      (a < Rb ∨ Rb + m ≤ a) → c₆.nmem a = c.nmem a := fun a h1 h2 h3 => by
    rw [m6 a h1 h3, m4 a (by omega), m2 a (by omega) h3]
  have e57 : c₆.nreg 7957 = c₂.nreg 7957 := by
    rw [hn6 _ (by omega) (by omega) (by omega), gn _ (by omega) (by omega) (by omega),
      q4 _ (by omega)]
  refine ⟨c₆, t₁ + (t₂ + (t₃ + (t₄ + (t₅ + t₆)))),
    Exec.seq e₁ (Exec.seq e₂ (Exec.seq e₃ (Exec.seq e₄ (Exec.seq e₅ e₆)))), by omega,
    τ₁.trans (finCongr e57.symm), τ₂, ⟨fun d => ?_, fun d => ?_, fun d => ?_, fun d => ?_,
      fun d => ?_, fun d => ?_, fun d => ?_, fun d => ?_⟩, mk, fun r hr => ?_,
    by rw [hr6, gr, lr, dr, br, ar], by rw [hrm6, grm, lrm, drm, brm, arm],
    by rw [ho6, go, lo, do_, bo, ao]⟩
  · -- RV
    have hσ := (σ d).2
    have := hK.rv d; simp only [Klein.iRV] at this ⊢
    rw [mk _ (by omega) (by omega) (by omega)]; exact this
  · -- NF
    have hσ := (σ d).2
    simp only [Klein.iNF]; exact h0 d
  · -- NE
    have hσ := (σ d).2
    have := hK.ne d; simp only [Klein.iNE] at this ⊢
    rw [mk _ (by omega) (by omega) (by omega)]; exact this
  · -- NG
    have hσ := (σ d).2
    have := hK.ng d; simp only [Klein.iNG] at this ⊢
    rw [mk _ (by omega) (by omega) (by omega)]; exact this
  · -- NT
    have hσ := (σ d).2
    simp only [Klein.iNT, Equiv.trans_apply, finCongr_apply, Fin.val_cast]
    rw [m6 _ (by omega) (by omega), m4 _ (by omega)]; exact b0 d
  · -- NH
    have hσ := (σ d).2
    simp only [Klein.iNH, Equiv.trans_apply, finCongr_apply, Fin.val_cast]
    rw [m6 _ (by omega) (by omega), l0 _ hσ, dm, hNH2, bR]
  · -- IS
    have hσ := (σ d).2
    have := hK.is d; simp only [Klein.iIS] at this ⊢
    rw [mk _ (by omega) (by omega) (by omega)]; exact this
  · -- ED
    have hσ := (σ d).2
    have h1 := hK.ed d; have := hE d; simp only [Klein.iED] at h1 ⊢
    rw [mk _ (by omega) (by omega) (by omega)]
    exact h1
  · rw [hn6 _ (by omega) (by omega) (by omega), gn _ (by omega) (by omega) (by omega)]
    exact fr r hr

end Map


section Lay

universe w

variable {D V F : Type w} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F] {M : CombMap D V F} {en : ℕ → D} {m : ℕ}

/-- **The node layout of the dual map with compact numbers** (`1 + gv` for the faces of `M`,
`2m + 1 + gf` for its vertices, `gv`, `gf` injective below `m`) on `n ≥ 4 m + 1` nodes. -/
theorem smLayoutC (h : NsStep.EnumOK M en m) {gv : F → ℕ} {gf : V → ℕ}
    (hgv : Function.Injective gv) (hgf : Function.Injective gf) (hlv : ∀ y, gv y < m)
    (hlf : ∀ v, gf v < m) {n : ℕ} (hn : 4 * m + 1 ≤ n) :
    Klein.Layout M.dual n (fun y => 1 + gv y) (ιG M h) (fun v => 2 * m + 1 + gf v) (ιE M h) := by
  have hF : Fintype.card F ≤ m := by
    calc Fintype.card F ≤ Fintype.card (Fin m) :=
          Fintype.card_le_of_injective (fun y => (⟨gv y, hlv y⟩ : Fin m))
            (fun a b e => hgv (congrArg Fin.val e))
      _ = m := Fintype.card_fin m
  have hV : Fintype.card V ≤ m := by
    calc Fintype.card V ≤ Fintype.card (Fin m) :=
          Fintype.card_le_of_injective (fun y => (⟨gf y, hlf y⟩ : Fin m))
            (fun a b e => hgf (congrArg Fin.val e))
      _ = m := Fintype.card_fin m
  have he : ∀ d, NegSSSP.eIx M (enEq h) d < m := NegSSSP.eIx_lt (enEq h)
  refine ⟨⟨fun x y e => hgv (by simpa using e), fun d => ?_, fun d d' e => ?_,
      fun x d => ?_, fun x => ?_, fun d => ?_⟩,
    ⟨fun x y e => hgf (by simpa using e), fun d => ?_, fun d d' e => ?_,
      fun x d => ?_, fun x => ?_, fun d => ?_⟩,
    by omega, by omega, fun x y => ?_, fun x d => ?_, fun d y => ?_, fun d d' => ?_⟩
  · show m + 1 + NegSSSP.eIx M (enEq h) (M.rev d) = _; rw [NegSSSP.eIx_rev]; rfl
  · exact NegSSSP.eIx_eq (M := M) (enEq h) (by simpa [ιG] using e)
  · have := hlv x; simp only [ιG]; omega
  · have := hlv x; omega
  · have := he d; simp only [ιG]; omega
  · show 3 * m + 1 + NegSSSP.eIx M (enEq h) (M.rev d) = _; rw [NegSSSP.eIx_rev]; rfl
  · exact NegSSSP.eIx_eq (M := M) (enEq h) (by simpa [ιE] using e)
  · have := hlf x; simp only [ιE]; omega
  · have := hlf x; omega
  · have := he d; simp only [ιE]; omega
  · have := hlv x; have := hlf y; omega
  · have := hlv x; simp only [ιE]; omega
  · have := he d; have := hlf y; simp only [ιG]; omega
  · have := he d; have := he d'; simp only [ιG, ιE]; omega

end Lay

end StEnc

end BKMNW

end PlanarFlow
