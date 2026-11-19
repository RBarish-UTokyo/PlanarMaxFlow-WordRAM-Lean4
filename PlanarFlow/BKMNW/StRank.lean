module

public import PlanarFlow.BKMNW.StBnd

/-!
# Compact node numbers: a rank pass and a relabelling pass

The frame numbers the faces of a piece map by orbit labels (`StEnc.ιF = fLab + 1`), an injective
numbering that is **not onto** an interval; the depth orders of `NegSSSP.toProg_orders` and the
cotree program `NegSSSP.cotProg_exec` need a numbering `of + τ` with `τ : X ≃ Fin n` onto. Here
the numbers are made compact on the machine (natural words only):

* `mkF A of n j` (`1` if some `A i - of = j`, `i < n`), `rkC f j` (the number of `j' < j` with
  `0 < f j'`), `rkC_succ`, `rkC_le`, `rkC_lt`;
* `rkZ` (zero the `N` words `R`), `rkMk` (mark `R[A i - of] := 1`), `rkPre` (the prefix ranks:
  `R[j] := rkC f j` where marked, the count in `r7930`), **`rkProg`** `= rkZ ; rkMk ; rkPre` and
  **`rkProg_exec`** (within `8 nA + 15 N + 12` steps, `R[j] = rkC mk j` at every marked `j`,
  `r7930 = rkC mk N`);
* `rlProg`, **`rlProg_exec`**: `X[i] := of + R[X[i] - of]` for `i < nA` (within `10 nA + 4`);
* **`rk_equiv`**: for an injective `ι : X → [of, of + N)` whose values are exactly the labels
  `A i`, `i < nA`, there is `τ : X ≃ Fin (rkC (mkF A of nA) N)` with `τ x = rkC mk (ι x - of)`
  (the compact number of `x`) and `0 < mk (ι x - of)`.

Registers: natural `7920 … 7924` (inputs `nA`, `Ab`, `of`, `N`, `Rb`), `7926 … 7931` (scratch;
`r7930` the count); `7940 … 7943` (inputs of `rlProg`: `nA`, `Xb`, `of`, `Rb`), `7944 … 7947`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace BKMNW

namespace StEnc

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs NegSSSP

/-! ### Marks and ranks -/

/-- `1` if some label `A i - of` (`i < n`) is `j`, else `0`. -/
def mkF (A : ℕ → ℕ) (of : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | i + 1, j => if A i - of = j then 1 else mkF A of i j

theorem mkF_le (A : ℕ → ℕ) (of : ℕ) : ∀ n j, mkF A of n j ≤ 1
  | 0, _ => by simp [mkF]
  | n + 1, j => by
    simp only [mkF]; split_ifs
    · exact le_refl _
    · exact mkF_le A of n j

theorem mkF_pos (A : ℕ → ℕ) (of : ℕ) : ∀ n j, 0 < mkF A of n j ↔ ∃ i < n, A i - of = j
  | 0, j => by simp [mkF]
  | n + 1, j => by
    simp only [mkF]
    split_ifs with h
    · exact ⟨fun _ => ⟨n, by omega, h⟩, fun _ => by omega⟩
    · rw [mkF_pos A of n j]
      constructor
      · rintro ⟨i, hi, e⟩; exact ⟨i, by omega, e⟩
      · rintro ⟨i, hi, e⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h' | rfl
        · exact ⟨i, h', e⟩
        · exact absurd e h

/-- The number of `j' < j` with `0 < f j'`. -/
def rkC (f : ℕ → ℕ) (j : ℕ) : ℕ := ((range j).filter (fun i => 0 < f i)).card

theorem rkC_succ (f : ℕ → ℕ) (j : ℕ) : rkC f (j + 1) = rkC f j + if 0 < f j then 1 else 0 := by
  unfold rkC
  rw [range_add_one, filter_insert]
  split_ifs with h
  · rw [card_insert_of_notMem (by simp)]
  · rfl

theorem rkC_le (f : ℕ → ℕ) (j : ℕ) : rkC f j ≤ j := by
  unfold rkC
  calc _ ≤ (range j).card := card_filter_le _ _
    _ = j := card_range j

theorem rkC_mono (f : ℕ → ℕ) {j k : ℕ} (h : j ≤ k) : rkC f j ≤ rkC f k :=
  card_le_card (filter_subset_filter _ (range_subset_range.2 h))

theorem rkC_lt (f : ℕ → ℕ) {j k : ℕ} (hf : 0 < f j) (h : j < k) : rkC f j < rkC f k := by
  have := rkC_mono f (show j + 1 ≤ k by omega)
  rw [rkC_succ, ite_eq_left_of_eq_true _ _ (eq_true hf)] at this
  omega

/-! ### The program -/

/-- Zero `R[j]`, `j < N` (`r7926 := 1`, `r7931 := 0`). -/
def rkZ : Stmt :=
  .seq (block [.constN 7926 1, .constN 7931 0, .constN 7927 0])
    (.whileLtN 7927 7923 (block [.addN 7928 7924 7927, .storeN 7928 7931, .addN 7927 7927 7926]))

/-- Mark `R[A i - of] := 1`, `i < nA`. -/
def rkMk : Stmt :=
  .seq (block [.constN 7927 0])
    (.whileLtN 7927 7920 (block [.addN 7928 7921 7927, .loadN 7928 7928, .subN 7928 7928 7922,
      .addN 7928 7924 7928, .storeN 7928 7926, .addN 7927 7927 7926]))

/-- One step of the prefix ranks. -/
def rkPreBody : Stmt :=
  .seq (block [.addN 7928 7924 7927, .loadN 7929 7928])
    (.seq (.ifLtN 7931 7929 (block [.storeN 7928 7930, .addN 7930 7930 7926]) .skip)
      (block [.addN 7927 7927 7926]))

/-- The prefix ranks: `R[j] := rkC f j` at the marked `j`, the count in `r7930`. -/
def rkPre : Stmt := .seq (block [.constN 7927 0, .constN 7930 0]) (.whileLtN 7927 7923 rkPreBody)

/-- **The rank pass.** -/
def rkProg : Stmt := .seq rkZ (.seq rkMk rkPre)

/-- **The relabelling pass**: `X[i] := of + R[X[i] - of]`, `i < nA`. -/
def rlProg : Stmt :=
  .seq (block [.constN 7944 1, .constN 7945 0])
    (.whileLtN 7945 7940 (block [.addN 7946 7941 7945, .loadN 7947 7946, .subN 7947 7947 7942,
      .addN 7947 7943 7947, .loadN 7947 7947, .addN 7947 7947 7942, .storeN 7946 7947,
      .addN 7945 7945 7944]))

theorem rkProg_natOnly : Klein.natOnly rkProg = true := by kernel_rfl

theorem rlProg_natOnly : Klein.natOnly rlProg = true := by kernel_rfl

variable {P : Input} {W : ℕ}

/-- The registers of the rank pass kept. -/
def RkR (c c' : Config) : Prop :=
  (∀ r, r < 7926 ∨ 7931 < r → c'.nreg r = c.nreg r) ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧
    c'.output = c.output

theorem rkZ_exec {N Rb : ℕ} (hW : Rb + N ≤ W) (h1W : 1 ≤ W) (c : Config) (hc : WordsBounded W c)
    (h23 : c.nreg 7923 = N) (h24 : c.nreg 7924 = Rb) :
    ∃ c' t, Exec P W rkZ c c' t ∧ t ≤ 5 * N + 5 ∧
      ((∀ j < N, c'.nmem (Rb + j) = 0) ∧ (∀ a, (a < Rb ∨ Rb + N ≤ a) → c'.nmem a = c.nmem a) ∧
        c'.nreg 7926 = 1 ∧ c'.nreg 7931 = 0 ∧ RkR c c') := by
  unfold rkZ
  refine spec_seq ?_
  exec_block
  all_goals try omega
  let J : ℕ → Config → Prop := fun i c' =>
    (∀ j < i, c'.nmem (Rb + j) = 0) ∧ (∀ a, (a < Rb ∨ Rb + i ≤ a) → c'.nmem a = c.nmem a) ∧
      c'.nreg 7926 = 1 ∧ c'.nreg 7931 = 0 ∧ RkR c c'
  refine spec_use (forLoop_exec (P := P) (a := 7927) (bR := 7923) J (K := 3) (n := N) _ ‹_›
    (by config_simp) (by config_simp; exact h23) ?_
    (fun i c₁ hi hw ha hb ⟨g0, g1, g26, g31, gn, gr, grm, go⟩ => by
      have e24 : c₁.nreg 7924 = Rb := (gn _ (by omega)).trans h24
      exec_block
      all_goals try ((try config_simp); (try simp only [e24, ha, g26]); omega)
      refine ⟨by omega, by config_simp; simp only [ha, g26], by config_simp; exact hb, ?_⟩
      dsimp only [J]
      refine ⟨fun j hj => ?_, fun a ha' => ?_, by config_simp; exact g26,
        by config_simp; exact g31, fun r hr => ?_, by config_simp; exact gr,
        by config_simp; exact grm, by config_simp; exact go⟩
      · config_simp; simp only [e24, ha, g31]
        rw [upd_apply]; split_ifs with h
        · rfl
        · exact g0 j (by omega)
      · config_simp; simp only [e24, ha]
        rw [upd_other _ _ _ (by omega)]; exact g1 a (by omega)
      · config_simp; simp only [upd_apply]; split_ifs <;> first | omega | exact gn r hr)) ?_
  · dsimp only [J]
    refine ⟨fun j hj => absurd hj (by omega), fun a _ => by config_simp, by config_simp,
      by config_simp, fun r hr => ?_, by config_simp, by config_simp, by config_simp⟩
    config_simp; simp only [upd_apply]; split_ifs <;> omega
  intro c₂ k₂ hk₂ _ ⟨_, g0, g1, g26, g31, gR⟩
  exact ⟨by omega, g0, g1, g26, g31, gR⟩

theorem rkMk_exec {nA Ab of N Rb : ℕ} {A : ℕ → ℕ} (hW : Rb + N ≤ W) (hAW : Ab + nA ≤ W)
    (hd : Ab + nA ≤ Rb ∨ Rb + N ≤ Ab) (hlt : ∀ i < nA, A i - of < N) (c : Config)
    (hc : WordsBounded W c) (h20 : c.nreg 7920 = nA) (h21 : c.nreg 7921 = Ab)
    (h22 : c.nreg 7922 = of) (h24 : c.nreg 7924 = Rb) (h26 : c.nreg 7926 = 1)
    (hA : ∀ i < nA, c.nmem (Ab + i) = A i) (hR : ∀ j < N, c.nmem (Rb + j) = 0) :
    ∃ c' t, Exec P W rkMk c c' t ∧ t ≤ 8 * nA + 3 ∧
      ((∀ j < N, c'.nmem (Rb + j) = mkF A of nA j) ∧
        (∀ a, (a < Rb ∨ Rb + N ≤ a) → c'.nmem a = c.nmem a) ∧
        c'.nreg 7926 = 1 ∧ RkR c c' ∧ (∀ r, r ≠ 7927 → r ≠ 7928 → c'.nreg r = c.nreg r)) := by
  unfold rkMk
  refine spec_seq ?_
  exec_block
  all_goals try omega
  let J : ℕ → Config → Prop := fun i c' =>
    (∀ j < N, c'.nmem (Rb + j) = mkF A of i j) ∧
      (∀ a, (a < Rb ∨ Rb + N ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, r ≠ 7927 → r ≠ 7928 → c'.nreg r = c.nreg r) ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧
      c'.output = c.output
  refine spec_use (forLoop_exec (P := P) (a := 7927) (bR := 7920) J (K := 6) (n := nA) _ ‹_›
    (by config_simp) (by config_simp; exact h20) ?_
    (fun i c₁ hi hw ha hb ⟨g0, g1, gn, gr, grm, go⟩ => by
      have e21 : c₁.nreg 7921 = Ab := (gn _ (by omega) (by omega)).trans h21
      have e22 : c₁.nreg 7922 = of := (gn _ (by omega) (by omega)).trans h22
      have e24 : c₁.nreg 7924 = Rb := (gn _ (by omega) (by omega)).trans h24
      have e26 : c₁.nreg 7926 = 1 := (gn _ (by omega) (by omega)).trans h26
      have eA : c₁.nmem (Ab + i) = A i := by rw [g1 _ (by omega)]; exact hA i hi
      have hl := hlt i hi
      exec_block
      all_goals try ((try config_simp); (try simp only [e21, e22, e24, e26, ha, eA]); omega)
      refine ⟨by omega, by config_simp; simp only [ha, e26], by config_simp; exact hb, ?_⟩
      dsimp only [J]
      refine ⟨fun j hj => ?_, fun a ha' => ?_, fun r h1 h2 => ?_, by config_simp; exact gr,
        by config_simp; exact grm, by config_simp; exact go⟩
      · config_simp; simp only [e21, e22, e24, e26, ha, eA]
        rw [upd_apply]; simp only [mkF]
        split_ifs with h h'
        · rfl
        · omega
        · omega
        · exact g0 j hj
      · config_simp; simp only [e21, e22, e24, e26, ha, eA]
        rw [upd_other _ _ _ (by omega)]; exact g1 a ha'
      · config_simp; simp only [upd_apply, h1, h2, ↓reduceIte]; exact gn r h1 h2)) ?_
  · dsimp only [J]
    refine ⟨fun j hj => by config_simp; simp only [mkF]; exact hR j hj, fun a _ => by config_simp,
      fun r h1 _ => ?_, by config_simp, by config_simp, by config_simp⟩
    config_simp; simp only [upd_apply, h1, ↓reduceIte]
  intro c₂ k₂ hk₂ _ ⟨_, g0, g1, gn, gr, grm, go⟩
  refine ⟨by omega, g0, g1, by rw [gn _ (by omega) (by omega)]; exact h26,
    ⟨fun r hr => gn r (by omega) (by omega), gr, grm, go⟩, gn⟩

/-- The `if` of the prefix step. -/
theorem rkIf_exec (c : Config) (hc : WordsBounded W c) (h31 : c.nreg 7931 = 0)
    (h26 : c.nreg 7926 = 1) (hb : c.nreg 7930 + 1 ≤ W) :
    ∃ c' k, Exec P W (.ifLtN 7931 7929 (block [.storeN 7928 7930, .addN 7930 7930 7926]) .skip)
      c c' k ∧ k ≤ 3 ∧
      (c'.nmem = (if 0 < c.nreg 7929 then upd c.nmem (c.nreg 7928) (c.nreg 7930) else c.nmem) ∧
        c'.nreg 7930 = c.nreg 7930 + (if 0 < c.nreg 7929 then 1 else 0) ∧
        (∀ r, r ≠ 7930 → c'.nreg r = c.nreg r) ∧
        c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output) := by
  by_cases h : 0 < c.nreg 7929
  · refine spec_ifLtN_true (by rw [h31]; exact h) ?_
    exec_block
    · config_simp; rw [h26]; exact hb
    refine ⟨by omega, by config_simp; simp only [h, ↓reduceIte], by config_simp; simp only [h,
      ↓reduceIte, h26], fun r hr => ?_, by config_simp, by config_simp, by config_simp⟩
    config_simp; simp only [upd_apply, hr, ↓reduceIte]
  · refine spec_ifLtN_false (by rw [h31]; exact h) ?_
    refine spec_skip hc ⟨by omega, by simp only [h, ↓reduceIte], by simp only [h, ↓reduceIte]; rfl,
      fun _ _ => rfl, rfl, rfl, rfl⟩

theorem rkPre_exec {N Rb : ℕ} {f : ℕ → ℕ} (hW : Rb + N ≤ W) (hNW : N + 1 ≤ W) (c : Config)
    (hc : WordsBounded W c) (h23 : c.nreg 7923 = N) (h24 : c.nreg 7924 = Rb)
    (h26 : c.nreg 7926 = 1) (h31 : c.nreg 7931 = 0) (hR : ∀ j < N, c.nmem (Rb + j) = f j) :
    ∃ c' t, Exec P W rkPre c c' t ∧ t ≤ 10 * N + 4 ∧
      ((∀ j < N, c'.nmem (Rb + j) = if 0 < f j then rkC f j else f j) ∧
        (∀ a, (a < Rb ∨ Rb + N ≤ a) → c'.nmem a = c.nmem a) ∧
        c'.nreg 7930 = rkC f N ∧ RkR c c') := by
  unfold rkPre
  refine spec_seq ?_
  exec_block
  all_goals try omega
  let J : ℕ → Config → Prop := fun j c' =>
    c'.nreg 7930 = rkC f j ∧
      (∀ j' < j, c'.nmem (Rb + j') = if 0 < f j' then rkC f j' else f j') ∧
      (∀ j', j ≤ j' → j' < N → c'.nmem (Rb + j') = f j') ∧
      (∀ a, (a < Rb ∨ Rb + N ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, r ≠ 7927 → r ≠ 7928 → r ≠ 7929 → r ≠ 7930 → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output
  refine spec_use (forLoop_exec (P := P) (a := 7927) (bR := 7923) J (K := 8) (n := N) _ ‹_›
    (by config_simp) (by config_simp; exact h23) ?_
    (fun j c₁ hj hw ha hb ⟨g30, g0, g1, g2, gn, gr, grm, go⟩ => by
      have e24 : c₁.nreg 7924 = Rb := (gn _ (by omega) (by omega) (by omega) (by omega)).trans h24
      have e26 : c₁.nreg 7926 = 1 := (gn _ (by omega) (by omega) (by omega) (by omega)).trans h26
      have e31 : c₁.nreg 7931 = 0 := (gn _ (by omega) (by omega) (by omega) (by omega)).trans h31
      have eR : c₁.nmem (Rb + j) = f j := g1 j le_rfl hj
      have hrk := rkC_le f j
      unfold rkPreBody
      refine spec_seq ?_
      exec_block
      all_goals try ((try config_simp); (try simp only [e24, ha]); omega)
      refine spec_seq ?_
      refine spec_use (rkIf_exec (P := P) _ ‹_› (by config_simp; exact e31)
        (by config_simp; exact e26) (by config_simp; rw [g30]; omega)) ?_
      intro c₂ k₂ hk₂ hw₂ ⟨a0, a30, an, ar, arm, ao⟩
      have f26 : c₂.nreg 7926 = 1 := by rw [an _ (by omega)]; config_simp; exact e26
      have f27 : c₂.nreg 7927 = j := by rw [an _ (by omega)]; config_simp; exact ha
      exec_block
      all_goals try ((try config_simp); (try simp only [f26, f27]); omega)
      config_simp at a0
      config_simp at a30
      simp only [e24, ha, eR] at a0 a30
      refine ⟨by omega, by config_simp; simp only [f26, f27], ?_, ?_⟩
      · config_simp; rw [an _ (by omega)]; config_simp; exact hb
      dsimp only [J]
      refine ⟨?_, ?_, ?_, ?_, fun r h1 h2 h3 h4 => ?_, ?_, ?_, ?_⟩ <;> config_simp
      · rw [a30, g30, rkC_succ]
      · intro j' hj'
        rw [a0]
        rcases Nat.lt_succ_iff_lt_or_eq.1 hj' with h' | rfl
        · have := g0 j' h'
          split_ifs at this ⊢ with p q <;>
            first | (rw [upd_other _ _ _ (by omega)]; exact this) | exact this
        · split_ifs with p
          · rw [upd_same, g30]
          · exact eR
      · intro j' h1 h2
        rw [a0]
        split_ifs with p
        · rw [upd_other _ _ _ (by omega)]; exact g1 j' (by omega) h2
        · exact g1 j' (by omega) h2
      · intro a ha'
        rw [a0]
        split_ifs with p
        · rw [upd_other _ _ _ (by omega)]; exact g2 a ha'
        · exact g2 a ha'
      · simp only [upd_apply, h1, ↓reduceIte]
        rw [an r h4]; config_simp
        simp only [upd_apply, h2, h3, ↓reduceIte]; exact gn r h1 h2 h3 h4
      · rw [ar]; config_simp; exact gr
      · rw [arm]; config_simp; exact grm
      · rw [ao]; config_simp; exact go)) ?_
  · dsimp only [J]
    refine ⟨by config_simp; simp [rkC], fun j hj => absurd hj (by omega),
      fun j _ hj => by config_simp; exact hR j hj, fun a _ => by config_simp,
      fun r h1 h2 h3 h4 => ?_, by config_simp, by config_simp, by config_simp⟩
    config_simp; simp only [upd_apply, h1, h4, ↓reduceIte]
  intro c₂ k₂ hk₂ _ ⟨_, g30, g0, g1, g2, gn, gr, grm, go⟩
  exact ⟨by omega, g0, g2, g30, fun r hr => gn r (by omega) (by omega) (by omega) (by omega), gr,
    grm, go⟩

/-- **The rank pass** (natural words only): from the labels `A i` (`i < nA`, at `Ab`) with
`A i - of < N`, the `N` words at `Rb` (disjoint from the labels) end with `R[j] = rkC mk j` at
every marked `j` (`mk = mkF A of nA`, `0 < mk j` iff `j = A i - of` for some `i < nA`) and
`r7930 = rkC mk N`, within `8 nA + 15 N + 12` steps; memory outside `[Rb, Rb + N)` kept;
registers outside `7926 … 7931` kept. -/
theorem rkProg_exec {nA Ab of N Rb : ℕ} {A : ℕ → ℕ} (hW : Rb + N ≤ W) (hAW : Ab + nA ≤ W)
    (hNW : N + 1 ≤ W) (hd : Ab + nA ≤ Rb ∨ Rb + N ≤ Ab) (hlt : ∀ i < nA, A i - of < N)
    (c : Config) (hc : WordsBounded W c) (h20 : c.nreg 7920 = nA) (h21 : c.nreg 7921 = Ab)
    (h22 : c.nreg 7922 = of) (h23 : c.nreg 7923 = N) (h24 : c.nreg 7924 = Rb)
    (hA : ∀ i < nA, c.nmem (Ab + i) = A i) :
    ∃ c' t, Exec P W rkProg c c' t ∧ t ≤ 8 * nA + 15 * N + 12 ∧
      ((∀ j < N, 0 < mkF A of nA j → c'.nmem (Rb + j) = rkC (mkF A of nA) j) ∧
        (∀ a, (a < Rb ∨ Rb + N ≤ a) → c'.nmem a = c.nmem a) ∧
        c'.nreg 7930 = rkC (mkF A of nA) N ∧ RkR c c') := by
  obtain ⟨c₁, t₁, e₁, ht₁, z0, z1, z26, z31, zR⟩ := rkZ_exec (P := P) hW (by omega) c hc h23 h24
  have q : ∀ r, r < 7926 ∨ 7931 < r → c₁.nreg r = c.nreg r := zR.1
  obtain ⟨c₂, t₂, e₂, ht₂, m0, m1, m26, mR, mn⟩ := rkMk_exec (P := P) (A := A) hW hAW hd hlt c₁
    e₁.wb_right ((q _ (by omega)).trans h20) ((q _ (by omega)).trans h21)
    ((q _ (by omega)).trans h22) ((q _ (by omega)).trans h24) z26
    (fun i hi => by rw [z1 _ (by omega)]; exact hA i hi) z0
  obtain ⟨c₃, t₃, e₃, ht₃, p0, p1, p30, pR⟩ := rkPre_exec (P := P) (f := mkF A of nA) hW hNW c₂
    e₂.wb_right ((mn _ (by omega) (by omega)).trans ((q _ (by omega)).trans h23))
    ((mn _ (by omega) (by omega)).trans ((q _ (by omega)).trans h24)) m26
    ((mn _ (by omega) (by omega)).trans z31) m0
  refine ⟨c₃, t₁ + (t₂ + t₃), Exec.seq e₁ (Exec.seq e₂ e₃), by omega,
    fun j hj hm => by rw [p0 j hj, ite_eq_left_of_eq_true _ _ (eq_true hm)], fun a ha => by rw [p1 a ha, m1 a ha, z1 a ha],
    p30, fun r hr => by rw [pR.1 r hr, mR.1 r hr, zR.1 r hr], by rw [pR.2.1, mR.2.1, zR.2.1],
    by rw [pR.2.2.1, mR.2.2.1, zR.2.2.1], by rw [pR.2.2.2, mR.2.2.2, zR.2.2.2]⟩

/-- **The relabelling pass**: `X[i] := of + R[X[i] - of]` for `i < nA` (the array `X` at `Xb`
disjoint from `R`, `X[i] - of < N`), within `10 nA + 4` steps; memory outside `[Xb, Xb + nA)`
kept; registers outside `7944 … 7947` kept. -/
theorem rlProg_exec {nA Xb of N Rb : ℕ} (hW : Rb + N ≤ W) (hXW : Xb + nA ≤ W) (h1W : 1 ≤ W)
    (hd : Xb + nA ≤ Rb ∨ Rb + N ≤ Xb) (c : Config) (hc : WordsBounded W c)
    (h40 : c.nreg 7940 = nA) (h41 : c.nreg 7941 = Xb) (h42 : c.nreg 7942 = of)
    (h43 : c.nreg 7943 = Rb) (hlt : ∀ i < nA, c.nmem (Xb + i) - of < N)
    (hv : ∀ i < nA, of + c.nmem (Rb + (c.nmem (Xb + i) - of)) ≤ W) :
    ∃ c' t, Exec P W rlProg c c' t ∧ t ≤ 10 * nA + 4 ∧
      ((∀ i < nA, c'.nmem (Xb + i) = of + c.nmem (Rb + (c.nmem (Xb + i) - of))) ∧
        (∀ a, (a < Xb ∨ Xb + nA ≤ a) → c'.nmem a = c.nmem a) ∧
        (∀ r, r < 7944 ∨ 7947 < r → c'.nreg r = c.nreg r) ∧ c'.rreg = c.rreg ∧
        c'.rmem = c.rmem ∧ c'.output = c.output) := by
  unfold rlProg
  refine spec_seq ?_
  exec_block
  all_goals try omega
  let J : ℕ → Config → Prop := fun i c' =>
    (∀ i' < i, c'.nmem (Xb + i') = of + c.nmem (Rb + (c.nmem (Xb + i') - of))) ∧
      (∀ a, (a < Xb ∨ Xb + i ≤ a) → c'.nmem a = c.nmem a) ∧ c'.nreg 7944 = 1 ∧
      (∀ r, r < 7944 ∨ 7947 < r → c'.nreg r = c.nreg r) ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧
      c'.output = c.output
  refine spec_use (forLoop_exec (P := P) (a := 7945) (bR := 7940) J (K := 8) (n := nA) _ ‹_›
    (by config_simp) (by config_simp; exact h40) ?_
    (fun i c₁ hi hw ha hb ⟨g0, g1, g44, gn, gr, grm, go⟩ => by
      have e41 : c₁.nreg 7941 = Xb := (gn _ (by omega)).trans h41
      have e42 : c₁.nreg 7942 = of := (gn _ (by omega)).trans h42
      have e43 : c₁.nreg 7943 = Rb := (gn _ (by omega)).trans h43
      have eX : c₁.nmem (Xb + i) = c.nmem (Xb + i) := g1 _ (by omega)
      have hl := hlt i hi
      have eR : c₁.nmem (Rb + (c.nmem (Xb + i) - of)) = c.nmem (Rb + (c.nmem (Xb + i) - of)) :=
        g1 _ (by omega)
      have hvi := hv i hi
      exec_block
      all_goals try ((try config_simp); (try simp only [e41, e42, e43, g44, ha, eX, eR]); omega)
      refine ⟨by omega, by config_simp; simp only [ha, g44], by config_simp; exact hb, ?_⟩
      dsimp only [J]
      refine ⟨fun i' hi' => ?_, fun a ha' => ?_, by config_simp; exact g44, fun r hr => ?_,
        by config_simp; exact gr, by config_simp; exact grm, by config_simp; exact go⟩
      · config_simp; simp only [e41, e42, e43, g44, ha, eX, eR]
        rw [upd_apply]
        split_ifs with h
        · have : i' = i := by omega
          subst this; omega
        · exact g0 i' (by omega)
      · config_simp; simp only [e41, ha]
        rw [upd_other _ _ _ (by omega)]; exact g1 a (by omega)
      · config_simp; simp only [upd_apply]; split_ifs <;> first | omega | exact gn r hr)) ?_
  · dsimp only [J]
    refine ⟨fun i hi => absurd hi (by omega), fun a _ => by config_simp, by config_simp,
      fun r hr => ?_, by config_simp, by config_simp, by config_simp⟩
    config_simp; simp only [upd_apply]; split_ifs <;> omega
  intro c₂ k₂ hk₂ _ ⟨_, g0, g1, _, gn, gr, grm, go⟩
  exact ⟨by omega, g0, g1, gn, gr, grm, go⟩

/-! ### The compact numbering -/

/-- **The compact numbering** of an injective numbering `ι : X → [of, of + N)` whose values are
exactly the labels `A i`, `i < nA`: `τ x = rkC mk (ι x - of)`, onto `Fin (rkC mk N)`. -/
theorem rk_equiv {X : Type*} [Fintype X] {ι : X → ℕ} (hinj : Function.Injective ι) {of N : ℕ}
    (hlo : ∀ x, of ≤ ι x) (hhi : ∀ x, ι x < of + N) {A : ℕ → ℕ} {nA : ℕ}
    (hA : ∀ i < nA, ∃ x, A i = ι x) (hX : ∀ x, ∃ i < nA, A i = ι x) :
    ∃ τ : X ≃ Fin (rkC (mkF A of nA) N),
      ∀ x, (τ x : ℕ) = rkC (mkF A of nA) (ι x - of) ∧ 0 < mkF A of nA (ι x - of) := by
  classical
  set mk := mkF A of nA with hmk
  have hpos : ∀ x, 0 < mk (ι x - of) := fun x => by
    obtain ⟨i, hi, e⟩ := hX x
    exact (mkF_pos A of nA _).2 ⟨i, hi, by rw [e]⟩
  have hlt : ∀ x, rkC mk (ι x - of) < rkC mk N := fun x =>
    rkC_lt mk (hpos x) (by have := hlo x; have := hhi x; omega)
  let g : X → Fin (rkC mk N) := fun x => ⟨rkC mk (ι x - of), hlt x⟩
  have ginj : Function.Injective g := by
    intro x y e
    have e' : rkC mk (ι x - of) = rkC mk (ι y - of) := congrArg Fin.val e
    apply hinj
    have := hlo x; have := hlo y
    rcases lt_trichotomy (ι x - of) (ι y - of) with h | h | h
    · exact absurd e' (Nat.ne_of_lt (rkC_lt mk (hpos x) h))
    · omega
    · exact absurd e'.symm (Nat.ne_of_lt (rkC_lt mk (hpos y) h))
  -- the marked indices below `N` are the values `ι x - of`
  have hcard : rkC mk N = Fintype.card X := by
    unfold rkC
    have e : (range N).filter (fun i => 0 < mk i) = univ.image (fun x => ι x - of) := by
      ext j
      simp only [mem_filter, mem_range, mem_image, mem_univ, true_and]
      constructor
      · rintro ⟨-, h⟩
        obtain ⟨i, hi, e⟩ := (mkF_pos A of nA j).1 h
        obtain ⟨x, hx⟩ := hA i hi
        exact ⟨x, by rw [← hx, e]⟩
      · rintro ⟨x, rfl⟩
        exact ⟨by have := hlo x; have := hhi x; omega, hpos x⟩
    rw [e, card_image_of_injective _ (fun x y h => hinj (by
      have := hlo x; have := hlo y; omega)), card_univ]
  have hbij : Function.Bijective g := by
    rw [Fintype.bijective_iff_injective_and_card]
    exact ⟨ginj, by rw [Fintype.card_fin, hcard]⟩
  exact ⟨Equiv.ofBijective g hbij, fun x => ⟨rfl, hpos x⟩⟩

end StEnc

end BKMNW

end PlanarFlow
