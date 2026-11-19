module

public import PlanarSeparator.Machine.MillerComp
public import PlanarSeparator.Machine.Front
public import PlanarSeparator.Machine.MillerHeavy

/-!
# Miller's separator on the machine: the heavy test at a level

With the coded map in memory (the reversals `A x` at `bR + x` and the vertices `V x` at
`bV + x` of the darts `x < 3 k`), the levels `L v` at `bLv + v`, a dart `fd v` at every vertex
at `bF + v`, the weights `w v` at `bw + v` (`v < n`) and their total in `r168`, the program
`hvy` decides whether the level `l` (in `r160`) is heavy:

* `fpass` flags the faces all of whose corners have level `≥ l` (at `bA + f`) and clears the
  labels;
* `clab` (`PlanarSeparator/Machine/MillerComp.lean`) labels their components;
* `wpass` adds the weight of every vertex of level `> l` to the label of the face of its dart
  `fd v` (at `bSum + c`) and sets the flag `r169` when a label exceeds `2/3` of the total.

`hvy_exec`: within `101 k + 21 n + 11` steps the flag is `1` exactly when some vertex `v` of
level `> l` gathers, with the vertices of level `> l` of the same label, more than `2/3` of the
total weight; the labels are those of `clab_exec`. For a coded triangulation with a breadth-first
tree, the flags are the faces off `zone (T.low l)` (`flagF_pos_iff`), and with
`PlanarSeparator.MillerProg.label_eq_iff` and `PlanarSeparator.MillerProg.heavy_iff` the test is
`PlanarSeparator.Map.Heavy` (`test_iff_heavy`, and for the whole program `hvy_heavy`).

Registers: those of `clab`, and `r160 = l`, `r161 = n`, `r162 = bV`, `r163 = bLv`, `r164 = bF`,
`r165 = bw`, `r166 = bSum`, `r168` the total weight; the program writes `r150 … r159`,
`r169 … r179`.
-/

@[expose] public section

namespace PlanarSeparator

namespace MillerProg

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs Finset

/-! ### The program -/

/-- The level of the corner `r171` of the face: `r173 := l - L (V r171)`. -/
def corner : List Instr :=
  [.addN 172 162 171, .loadN 173 172, .addN 172 163 173, .loadN 173 172, .subN 173 160 173]

/-- **One face** `r170 = f`: flag it if its corners have level `≥ l`, and clear its label. -/
def fbody : Stmt :=
  .seq (block ([.mulN 171 142 170] ++ corner ++ [.copyN 174 173, .addN 171 171 141] ++ corner ++
    [.addN 174 174 173, .addN 171 171 141] ++ corner ++ [.addN 174 174 173, .copyN 177 141]))
    (.seq (.ifLtN 140 174 (.instr (.copyN 177 140)) .skip)
      (block [.addN 172 144 170, .storeN 172 177, .addN 172 145 170, .storeN 172 140,
        .addN 170 170 141]))

/-- **The flags.** -/
def fpass : Stmt := .seq (.instr (.copyN 170 140)) (.whileLtN 170 143 fbody)

/-- **One vertex** `r170 = v` of level `> l`: add its weight to the label `r175` of the face of
its dart, and set the flag if the label now weighs more than `2/3` of the total. -/
def wadd : Stmt :=
  .seq (block [.addN 172 164 170, .loadN 174 172, .divN 174 174 142, .addN 172 145 174,
    .loadN 175 172, .addN 172 166 175, .loadN 176 172, .addN 177 165 170, .loadN 178 177,
    .addN 176 176 178, .storeN 172 176, .mulN 176 176 142, .addN 178 168 168])
    (.ifLtN 178 176 (.instr (.copyN 169 141)) .skip)

/-- **One vertex** `r170 = v`. -/
def wbody : Stmt :=
  .seq (block [.addN 172 163 170, .loadN 173 172])
    (.seq (.ifLtN 160 173 wadd .skip) (.instr (.addN 170 170 141)))

/-- **The weights of the labels and the flag.** -/
def wpass : Stmt := .seq (block [.copyN 170 140, .copyN 169 140]) (.whileLtN 170 161 wbody)

/-- **The heavy test.** -/
def hvy : Stmt := .seq fpass (.seq clab wpass)

/-- The registers of the heavy test. -/
structure HR (l n bV bLv bF bw bSum : ℕ) (c : Config) : Prop where
  r160 : c.nreg 160 = l
  r161 : c.nreg 161 = n
  r162 : c.nreg 162 = bV
  r163 : c.nreg 163 = bLv
  r164 : c.nreg 164 = bF
  r165 : c.nreg 165 = bw
  r166 : c.nreg 166 = bSum

theorem HR.of {l n bV bLv bF bw bSum : ℕ} {c c' : Config} (h : HR l n bV bLv bF bw bSum c)
    (e : ∀ r, 160 ≤ r → r < 167 → c'.nreg r = c.nreg r) : HR l n bV bLv bF bw bSum c' :=
  ⟨(e _ (by omega) (by omega)).trans h.r160, (e _ (by omega) (by omega)).trans h.r161,
    (e _ (by omega) (by omega)).trans h.r162, (e _ (by omega) (by omega)).trans h.r163,
    (e _ (by omega) (by omega)).trans h.r164, (e _ (by omega) (by omega)).trans h.r165,
    (e _ (by omega) (by omega)).trans h.r166⟩

/-- The flag of a face: all corners of level `≥ l`. -/
def flagF (l : ℕ) (V L : ℕ → ℕ) (f : ℕ) : ℕ :=
  if l ≤ L (V (3 * f)) ∧ l ≤ L (V (3 * f + 1)) ∧ l ≤ L (V (3 * f + 2)) then 1 else 0

/-! ### The flags -/

section proofs

variable {k : ℕ} {A : ℕ → ℕ} {bA bL bS bR : ℕ} {W : ℕ} {P : Input}
  {l n bV bLv bF bw bSum : ℕ} {V L : ℕ → ℕ}

set_option linter.unusedSimpArgs false in
set_option linter.unusedTactic false in
theorem fpass_exec (hlay : bV + 3 * k ≤ bA ∧ bLv + n ≤ bA ∧ bA + k ≤ bL)
    (hW : bA + 3 * k + 3 * l + n ≤ W ∧ bL + k ≤ W)
    (c : Config) (hc : WordsBounded W c) (hR : CR k bA bL bS bR c)
    (hH : HR l n bV bLv bF bw bSum c) (hV : ∀ x < 3 * k, c.nmem (bV + x) = V x ∧ V x < n)
    (hL : ∀ v < n, c.nmem (bLv + v) = L v) :
    ∃ c' t, Exec P W fpass c c' t ∧ t ≤ 33 * k + 3 ∧
      (∀ f < k, c'.nmem (bA + f) = flagF l V L f ∧ c'.nmem (bL + f) = 0) ∧
      (∀ r, r < 170 ∨ 180 ≤ r → c'.nreg r = c.nreg r) ∧
      (∀ a, a < bA ∨ bL + k ≤ a → c'.nmem a = c.nmem a) ∧ c'.output = c.output := by
  obtain ⟨r140, r141, r142, r143, r144, r145, r146, r147⟩ := hR
  obtain ⟨r160, r161, r162, r163, r164, r165, r166⟩ := hH
  let I : ℕ → Config → Prop := fun i c' => WordsBounded W c' ∧ c'.nreg 170 = i ∧
    c'.nreg 143 = k ∧ i ≤ k ∧
    (∀ f < i, c'.nmem (bA + f) = flagF l V L f ∧ c'.nmem (bL + f) = 0) ∧
    (∀ r, r < 170 ∨ 180 ≤ r → c'.nreg r = c.nreg r) ∧
    (∀ a, (a < bA ∨ bL + k ≤ a ∨ (bA + i ≤ a ∧ a < bA + k) ∨ (bL + i ≤ a ∧ a < bL + k)) →
      c'.nmem a = c.nmem a) ∧ c'.output = c.output
  have e₁ := Exec.copyN (P := P) hc 170 140
  obtain ⟨c', t, e, hI, ht⟩ := Exec.forN (P := P) (W := W) (ri := 170) (rN := 143) (N := k)
    (lo := 0) (B := 31) (body := fbody) I (fun i c' h => ⟨h.1, h.2.1, h.2.2.1⟩)
    (fun i c₁ ⟨hw, h170, h143, hik, hdone, hr, hf, ho⟩ hi => by
      have g : ∀ r, r < 170 → c₁.nreg r = c.nreg r := fun r hr' => hr r (Or.inl hr')
      have g160 : c₁.nreg 160 = l := by rw [g 160 (by omega)]; exact r160
      have g162 : c₁.nreg 162 = bV := by rw [g 162 (by omega)]; exact r162
      have g163 : c₁.nreg 163 = bLv := by rw [g 163 (by omega)]; exact r163
      have g140 : c₁.nreg 140 = 0 := by rw [g 140 (by omega)]; exact r140
      have g141 : c₁.nreg 141 = 1 := by rw [g 141 (by omega)]; exact r141
      have g142 : c₁.nreg 142 = 3 := by rw [g 142 (by omega)]; exact r142
      have g144 : c₁.nreg 144 = bA := by rw [g 144 (by omega)]; exact r144
      have g145 : c₁.nreg 145 = bL := by rw [g 145 (by omega)]; exact r145
      have hv : ∀ j < 3, c₁.nmem (bV + (3 * i + j)) = V (3 * i + j) ∧ V (3 * i + j) < n :=
        fun j hj => by rw [hf _ (Or.inl (by omega))]; exact hV _ (by omega)
      have hl : ∀ j < 3, c₁.nmem (bLv + V (3 * i + j)) = L (V (3 * i + j)) :=
        fun j hj => by have := (hv j hj).2; rw [hf _ (Or.inl (by omega))]; exact hL _ this
      have m0 : c₁.nmem (bV + 3 * i) = V (3 * i) := (hv 0 (by omega)).1
      have m1 : c₁.nmem (bV + (3 * i + 1)) = V (3 * i + 1) := (hv 1 (by omega)).1
      have m2 : c₁.nmem (bV + (3 * i + 1 + 1)) = V (3 * i + 2) := (hv 2 (by omega)).1
      have n0 : V (3 * i) < n := (hv 0 (by omega)).2
      have n1 := (hv 1 (by omega)).2
      have n2 := (hv 2 (by omega)).2
      have q0 : c₁.nmem (bLv + V (3 * i)) = L (V (3 * i)) := hl 0 (by omega)
      have q1 : c₁.nmem (bLv + V (3 * i + 1)) = L (V (3 * i + 1)) := hl 1 (by omega)
      have q2 : c₁.nmem (bLv + V (3 * i + 2)) = L (V (3 * i + 2)) := hl 2 (by omega)
      unfold fbody corner
      simp only [List.cons_append, List.nil_append]
      refine spec_seq ?_
      exec_block
      all_goals try (config_simp; (try simp only [h170, g142, g162, g163, g141, g160, g140,
        g144, g145, m0, m1, m2]); config_simp; (try simp only [m0, m1, m2, q0, q1, q2]); omega)
      rename_i hwb
      simp only [h170, g142, g162, g163, g141, g160, m0, m1, m2] at hwb ⊢
      config_simp
      simp only [q0, q1, q2] at hwb ⊢
      have post : ∀ (c₂ : Config) (v : ℕ), WordsBounded W c₂ → c₂.nreg 170 = i + 1 →
          (∀ r, r < 170 ∨ 180 ≤ r → c₂.nreg r = c₁.nreg r) →
          (∀ a, a ≠ bA + i → a ≠ bL + i → c₂.nmem a = c₁.nmem a) →
          c₂.nmem (bA + i) = v → v = flagF l V L i → c₂.nmem (bL + i) = 0 →
          c₂.output = c₁.output → I (i + 1) c₂ := by
        intro c₂ v hw2 h1 h2 h3 h4 h5 h6 h7
        refine ⟨hw2, h1, by rw [h2 143 (by omega)]; exact h143, by omega, fun f hf => ?_,
          fun r hr' => by rw [h2 r hr', hr r hr'], fun a ha => ?_, by rw [h7, ho]⟩
        · rcases Nat.lt_succ_iff_lt_or_eq.1 hf with hf | rfl
          · rw [h3 _ (by omega) (by omega), h3 _ (by omega) (by omega)]; exact hdone f hf
          · exact ⟨h4.trans h5, h6⟩
        · rw [h3 _ (by omega) (by omega)]; exact hf a (by omega)
      unfold flagF at post
      refine spec_seq ?_
      by_cases hs : 0 < l - L (V (3 * i)) + (l - L (V (3 * i + 1))) + (l - L (V (3 * i + 2)))
      · refine spec_ifLtN_true (by config_simp; rw [g140]; exact hs) ?_
        refine spec_instr (Exec.copyN ‹_› 177 140) fun hw => ?_
        exec_block
        all_goals try (config_simp; (try simp only [h170, g144, g145, g141]); omega)
        refine ⟨post _ 0 ‹_› (by config_simp; rw [h170, g141]) (fun r hr' => by
          config_simp; simp only [upd_apply]; split_ifs <;> omega) (fun a h1 h2 => by
          config_simp; rw [g145, g144, h170, upd_other _ _ _ (by omega),
            upd_other _ _ _ (by omega)]) (by config_simp; rw [g145, g144, h170,
            upd_other _ _ _ (by omega), upd_same, g140]) (by split_ifs <;> omega)
          (by config_simp; rw [g145, h170, upd_same, g140]) (by config_simp), by omega⟩
      · refine spec_ifLtN_false (by config_simp; rw [g140]; exact hs) ?_
        refine spec_skip ‹_› ?_
        exec_block
        all_goals try (config_simp; (try simp only [h170, g144, g145, g141]); omega)
        refine ⟨post _ 1 ‹_› (by config_simp; rw [h170, g141]) (fun r hr' => by
          config_simp; simp only [upd_apply]; split_ifs <;> omega) (fun a h1 h2 => by
          config_simp; rw [g145, g144, h170, upd_other _ _ _ (by omega),
            upd_other _ _ _ (by omega)]) (by config_simp; rw [g145, g144, h170,
            upd_other _ _ _ (by omega), upd_same]) (by split_ifs <;> omega)
          (by config_simp; rw [g145, h170, upd_same, g140]) (by config_simp), by omega⟩)
    (by omega) ⟨e₁.wb_right, by config_simp; exact r140, by config_simp; exact r143, by omega,
      fun f hf => absurd hf (by omega), fun r hr => by
        show upd c.nreg 170 (c.nreg 140) r = c.nreg r
        simp only [upd_apply]; split_ifs <;> omega, fun a _ => rfl, rfl⟩
  obtain ⟨-, -, -, -, hdone', hr', hf', ho'⟩ := hI
  exact ⟨c', 1 + t, .seq e₁ e, by omega, hdone', hr', fun a ha => hf' a (by omega), ho'⟩

/-! ### The weights of the labels -/

/-- The weight of the label `c` among the vertices `u < i` of level `> l`, the label of `u` being
`lb (fd u / 3)`. -/
noncomputable def sm (l : ℕ) (L fd lb w : ℕ → ℕ) (i c : ℕ) : ℕ :=
  ∑ u ∈ range i, if l < L u ∧ lb (fd u / 3) = c then w u else 0

theorem sm_succ (l : ℕ) (L fd lb w : ℕ → ℕ) (i c : ℕ) :
    sm l L fd lb w (i + 1) c =
      sm l L fd lb w i c + if l < L i ∧ lb (fd i / 3) = c then w i else 0 := by
  unfold sm; rw [sum_range_succ]

theorem sm_le (l : ℕ) (L fd lb w : ℕ → ℕ) (i c : ℕ) :
    sm l L fd lb w i c ≤ ∑ u ∈ range i, w u :=
  sum_le_sum fun u _ => by split_ifs <;> omega

theorem flag_step {k x T : ℕ} {f g : ℕ → ℕ} (hg : ∀ y, y ≠ x → g y = f y) (hx : f x ≤ g x) :
    (∃ y ≤ k, T < 3 * g y) ↔ (∃ y ≤ k, T < 3 * f y) ∨ (x ≤ k ∧ T < 3 * g x) := by
  constructor
  · rintro ⟨y, hy, h⟩
    by_cases e : y = x
    · subst e; exact Or.inr ⟨hy, h⟩
    · exact Or.inl ⟨y, hy, by rwa [← hg y e]⟩
  · rintro (⟨y, hy, h⟩ | ⟨hy, h⟩)
    · by_cases e : y = x
      · subst e; exact ⟨y, hy, by omega⟩
      · exact ⟨y, hy, by rwa [hg y e]⟩
    · exact ⟨x, hy, h⟩

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
set_option linter.unusedTactic false in
theorem wpass_exec {fd lb w : ℕ → ℕ} {tot : ℕ}
    (hlay : bLv + n ≤ bA ∧ bF + n ≤ bA ∧ bw + n ≤ bA ∧ bA + k ≤ bL ∧ bL + k ≤ bSum)
    (hW : bSum + k + 1 + n ≤ W ∧ 3 * tot ≤ W) (htot : ∑ u ∈ range n, w u = tot)
    (c : Config) (hc : WordsBounded W c) (hR : CR k bA bL bS bR c)
    (hH : HR l n bV bLv bF bw bSum c) (h168 : c.nreg 168 = tot)
    (hL : ∀ v < n, c.nmem (bLv + v) = L v) (hF : ∀ v < n, c.nmem (bF + v) = fd v ∧ fd v < 3 * k)
    (hw : ∀ v < n, c.nmem (bw + v) = w v) (hlb : ∀ g < k, c.nmem (bL + g) = lb g ∧ lb g ≤ k)
    (hz : ∀ x ≤ k, c.nmem (bSum + x) = 0) :
    ∃ c' t, Exec P W wpass c c' t ∧ t ≤ 21 * n + 4 ∧ c'.nreg 169 ≤ 1 ∧
      (c'.nreg 169 = 1 ↔ ∃ x ≤ k, 2 * tot < 3 * sm l L fd lb w n x) ∧
      (∀ x ≤ k, c'.nmem (bSum + x) = sm l L fd lb w n x) ∧
      (∀ r, r < 169 ∨ 180 ≤ r → c'.nreg r = c.nreg r) ∧
      (∀ a, a < bSum ∨ bSum + k + 1 ≤ a → c'.nmem a = c.nmem a) ∧ c'.output = c.output := by
  obtain ⟨r140, r141, r142, r143, r144, r145, r146, r147⟩ := hR
  obtain ⟨r160, r161, r162, r163, r164, r165, r166⟩ := hH
  let I : ℕ → Config → Prop := fun i c' => WordsBounded W c' ∧ c'.nreg 170 = i ∧
    c'.nreg 161 = n ∧ i ≤ n ∧ c'.nreg 169 ≤ 1 ∧
    (c'.nreg 169 = 1 ↔ ∃ x ≤ k, 2 * tot < 3 * sm l L fd lb w i x) ∧
    (∀ x ≤ k, c'.nmem (bSum + x) = sm l L fd lb w i x) ∧
    (∀ r, r < 169 ∨ 180 ≤ r → c'.nreg r = c.nreg r) ∧
    (∀ a, a < bSum ∨ bSum + k + 1 ≤ a → c'.nmem a = c.nmem a) ∧ c'.output = c.output
  obtain ⟨c₁, k₁, e₁, hI₁, rfl⟩ : ∃ c₁ k₁, Exec P W (block [.copyN 170 140, .copyN 169 140])
      c c₁ k₁ ∧ I 0 c₁ ∧ k₁ = 2 := by
    exec_block
    refine ⟨⟨‹_›, by config_simp; exact r140, by config_simp; exact r161, by omega,
      by config_simp; omega, ?_, fun x hx => by config_simp; rw [hz x hx]; simp [sm],
      fun r hr => by config_simp; simp only [upd_apply]; split_ifs <;> omega,
      fun a _ => rfl, rfl⟩, rfl⟩
    config_simp; rw [r140]; simp [sm]
  obtain ⟨c', t, e, hI, ht⟩ := Exec.forN (P := P) (W := W) (ri := 170) (rN := 161) (N := n)
    (lo := 0) (B := 19) (body := wbody) I (fun i c' h => ⟨h.1, h.2.1, h.2.2.1⟩)
    (fun i c₁ ⟨hw₁, h170, h161, hin, hfl, hfl', hS, hr, hf, ho⟩ hi => by
      have g : ∀ r, r < 169 → c₁.nreg r = c.nreg r := fun r hr' => hr r (Or.inl hr')
      have g160 : c₁.nreg 160 = l := by rw [g 160 (by omega)]; exact r160
      have g163 : c₁.nreg 163 = bLv := by rw [g 163 (by omega)]; exact r163
      have g164 : c₁.nreg 164 = bF := by rw [g 164 (by omega)]; exact r164
      have g165 : c₁.nreg 165 = bw := by rw [g 165 (by omega)]; exact r165
      have g166 : c₁.nreg 166 = bSum := by rw [g 166 (by omega)]; exact r166
      have g168 : c₁.nreg 168 = tot := by rw [g 168 (by omega)]; exact h168
      have g141 : c₁.nreg 141 = 1 := by rw [g 141 (by omega)]; exact r141
      have g142 : c₁.nreg 142 = 3 := by rw [g 142 (by omega)]; exact r142
      have g145 : c₁.nreg 145 = bL := by rw [g 145 (by omega)]; exact r145
      have mL : c₁.nmem (bLv + i) = L i := by rw [hf _ (Or.inl (by omega))]; exact hL i hi
      have mF : c₁.nmem (bF + i) = fd i := by rw [hf _ (Or.inl (by omega))]; exact (hF i hi).1
      have mw : c₁.nmem (bw + i) = w i := by rw [hf _ (Or.inl (by omega))]; exact hw i hi
      have hfk : fd i / 3 < k := by have := (hF i hi).2; omega
      have mb : c₁.nmem (bL + fd i / 3) = lb (fd i / 3) := by
        rw [hf _ (Or.inl (by omega))]; exact (hlb _ hfk).1
      have hlbk := (hlb _ hfk).2
      have mS : c₁.nmem (bSum + lb (fd i / 3)) = sm l L fd lb w i (lb (fd i / 3)) :=
        hS _ hlbk
      have hsm := sm_le l L fd lb w (i + 1) (lb (fd i / 3))
      have hwle : ∑ u ∈ range (i + 1), w u ≤ tot := by
        rw [← htot]; exact sum_le_sum_of_subset (range_subset_range.2 (by omega))
      have hsm1 := sm_succ l L fd lb w i (lb (fd i / 3))
      unfold wbody
      refine spec_seq ?_
      exec_block
      · config_simp; rw [g163, h170]; omega
      rename_i hwb
      simp only [g163, h170, mL] at hwb ⊢
      refine spec_seq ?_
      by_cases hli : l < L i
      · rw [ite_eq_left ⟨hli, rfl⟩] at hsm1
        refine spec_ifLtN_true (by config_simp; rw [g160]; exact hli) ?_
        unfold wadd
        refine spec_seq ?_
        exec_block
        all_goals try (config_simp; (try simp only [g164, h170, mF, g142, g145, mb, g166, mS,
          g165, mw, g168]); omega)
        rename_i hwc
        simp only [g164, h170, mF, g142, g145, mb, g166, mS, g165, mw, g168] at hwc ⊢
        set x := lb (fd i / 3) with hx
        have hsmx : ∀ y, y ≠ x → sm l L fd lb w (i + 1) y = sm l L fd lb w i y := fun y hy => by
          rw [sm_succ, ite_eq_right (fun h => hy h.2.symm)]; rfl
        have hfs := flag_step (k := k) (T := 2 * tot) hsmx (by omega)
        have post : ∀ (c₂ : Config), WordsBounded W c₂ → c₂.nreg 170 = i + 1 →
            c₂.nreg 169 ≤ 1 → (c₂.nreg 169 = 1 ↔ c₁.nreg 169 = 1 ∨
              (x ≤ k ∧ 2 * tot < 3 * sm l L fd lb w (i + 1) x)) →
            (∀ r, r < 169 ∨ 180 ≤ r → c₂.nreg r = c₁.nreg r) →
            c₂.nmem = upd c₁.nmem (bSum + x) (sm l L fd lb w i x + w i) →
            c₂.output = c₁.output → I (i + 1) c₂ := by
          intro c₂ hw2 h1 h2 h3 h4 h5 h6
          refine ⟨hw2, h1, by rw [h4 161 (by omega)]; exact h161, by omega, h2,
            by rw [h3, hfl', hfs], fun y hy => ?_, fun r hr' => by rw [h4 r hr', hr r hr'],
            fun a ha => by rw [h5, upd_other _ _ _ (by omega)]; exact hf a ha,
            by rw [h6, ho]⟩
          rw [h5]
          by_cases e : y = x
          · subst e; rw [upd_same]; omega
          · rw [upd_other _ _ _ (by omega), hS y hy, hsmx y e]
        by_cases hb : tot + tot < (sm l L fd lb w i x + w i) * 3
        · refine spec_ifLtN_true (by config_simp; exact hb) ?_
          refine spec_instr (Exec.copyN ‹_› 169 141) fun hw => ?_
          refine spec_instr (Exec.addN hw _ _ _ (by config_simp; rw [h170, g141]; omega))
            fun hw' => ⟨post _ hw' (by config_simp; rw [h170, g141]) (by config_simp; omega)
            (by config_simp; rw [g141]; simp only [true_iff]; exact Or.inr ⟨hlbk, by omega⟩)
            (fun r hr' => by config_simp; simp only [upd_apply]; split_ifs <;> omega)
            (by config_simp) (by config_simp), by omega⟩
        · refine spec_ifLtN_false (by config_simp; exact hb) ?_
          refine spec_skip ‹_› ?_
          refine spec_instr (Exec.addN ‹_› _ _ _ (by config_simp; rw [h170, g141]; omega))
            fun hw' => ⟨post _ hw' (by config_simp; rw [h170, g141]) (by config_simp; omega)
            (by config_simp; constructor
                · exact Or.inl
                · rintro (h | ⟨-, h⟩)
                  · exact h
                  · omega)
            (fun r hr' => by config_simp; simp only [upd_apply]; split_ifs <;> omega)
            (by config_simp) (by config_simp), by omega⟩
      · have hsmy : ∀ y, sm l L fd lb w (i + 1) y = sm l L fd lb w i y := fun y => by
          rw [sm_succ, ite_eq_right (fun h => hli h.1)]; rfl
        refine spec_ifLtN_false (by config_simp; rw [g160]; exact hli) ?_
        refine spec_skip ‹_› ?_
        refine spec_instr (Exec.addN ‹_› _ _ _ (by config_simp; rw [h170, g141]; omega))
          fun hw' => ⟨⟨hw', by config_simp; rw [h170, g141], by config_simp; exact h161,
            by omega, by config_simp; exact hfl, by config_simp; simp only [hsmy]; exact hfl',
            fun y hy => by config_simp; rw [hsmy]; exact hS y hy, fun r hr' => by
            config_simp; simp only [upd_apply]; split_ifs <;> first | omega | exact hr r hr',
            fun a ha => by config_simp; exact hf a ha, by config_simp; exact ho⟩, by omega⟩)
    (by omega) hI₁
  obtain ⟨-, -, -, -, hfl1, hfl, hS', hr', hf', ho'⟩ := hI
  exact ⟨c', 2 + t, .seq e₁ e, by omega, hfl1, hfl, hS', hr', hf', ho'⟩

/-! ### The heavy test -/

theorem exists_of_sm {l : ℕ} {L fd lb w : ℕ → ℕ} {n x T : ℕ} (h : T < 3 * sm l L fd lb w n x) :
    ∃ u < n, l < L u ∧ lb (fd u / 3) = x := by
  by_contra hne
  push Not at hne
  have : sm l L fd lb w n x = 0 := sum_eq_zero fun u hu => by
    rw [ite_eq_right]; exact fun h' => hne u (mem_range.1 hu) h'.1 h'.2
  omega

/-- **The heavy test at level `l`.** The flag `r169` is `1` exactly when some vertex `v` of level
`> l` has, with the vertices of level `> l` of the same label, more than `2/3` of the total
weight; the labels `lb` are the components of the faces flagged by `flagF` (`clab_exec`), and
the labels are left at `bL` and the weight `sm l L fd lb w n x` of the vertices of level `> l`
of each label `x` at `bSum + x`. -/
theorem hvy_exec {fd w : ℕ → ℕ} {tot : ℕ} (hA : RevOk k A)
    (hlay : bR + 3 * k ≤ bA ∧ bV + 3 * k ≤ bA ∧ bLv + n ≤ bA ∧ bF + n ≤ bA ∧ bw + n ≤ bA ∧
      bA + k ≤ bL ∧ bL + k ≤ bS ∧ bS + k ≤ bSum)
    (hW : bSum + 3 * k + 3 * l + n + 1 ≤ W ∧ 3 * tot ≤ W) (htot : ∑ u ∈ range n, w u = tot)
    (c : Config) (hc : WordsBounded W c) (hR : CR k bA bL bS bR c)
    (hH : HR l n bV bLv bF bw bSum c) (h168 : c.nreg 168 = tot)
    (hAm : ∀ x < 3 * k, c.nmem (bR + x) = A x)
    (hV : ∀ x < 3 * k, c.nmem (bV + x) = V x ∧ V x < n)
    (hL : ∀ v < n, c.nmem (bLv + v) = L v) (hF : ∀ v < n, c.nmem (bF + v) = fd v ∧ fd v < 3 * k)
    (hw : ∀ v < n, c.nmem (bw + v) = w v) (hz : ∀ x ≤ k, c.nmem (bSum + x) = 0) :
    ∃ c' t, Exec P W hvy c c' t ∧ t ≤ 101 * k + 21 * n + 11 ∧
      ∃ lb : ℕ → ℕ, (∀ g < k, lb g = 0 ↔ flagF l V L g = 0) ∧
      (∀ f < k, ∀ g < k, 0 < flagF l V L f → 0 < flagF l V L g →
        (lb f = lb g ↔ Relation.ReflTransGen (FA k A (flagF l V L)) f g)) ∧
      c'.nreg 169 ≤ 1 ∧ (c'.nreg 169 = 1 ↔ ∃ v < n, l < L v ∧
        2 * tot < 3 * ∑ u ∈ range n, if l < L u ∧ lb (fd u / 3) = lb (fd v / 3) then w u else 0) ∧
      (∀ x ≤ k, c'.nmem (bSum + x) = sm l L fd lb w n x) ∧
      (∀ g < k, c'.nmem (bL + g) = lb g ∧ lb g ≤ k) ∧
      (∀ r, r < 150 ∨ (160 ≤ r ∧ r < 169) ∨ 180 ≤ r → c'.nreg r = c.nreg r) ∧
      (∀ a, a < bA ∨ bSum + k + 1 ≤ a → c'.nmem a = c.nmem a) ∧ c'.output = c.output := by
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8⟩ := hlay
  unfold hvy
  obtain ⟨c₁, t₁, e₁, ht₁, hfl₁, hr₁, hf₁, ho₁⟩ := fpass_exec (P := P) (k := k) (bS := bS)
    (bR := bR) (bF := bF) (bw := bw) (bSum := bSum) ⟨l2, l3, l6⟩ ⟨by omega, by omega⟩ c hc hR hH
    hV hL
  have hR₁ : CR k bA bL bS bR c₁ := hR.of fun r hr => hr₁ r (Or.inl (by omega))
  obtain ⟨c₂, t₂, e₂, ht₂, lb, hlb, hcc, hle, hz0, hcls, hr₂, hf₂, ho₂⟩ :=
    clab_exec (P := P) (Av := flagF l V L) hA ⟨l1, l6, l7⟩ (by omega) c₁ e₁.wb_right hR₁
      (fun x hx => by rw [hf₁ _ (Or.inl (by omega))]; exact hAm x hx)
      (fun f hf => (hfl₁ f hf).1) (fun g hg => (hfl₁ g hg).2)
  have hR₂ : CR k bA bL bS bR c₂ := hR₁.of fun r hr => hr₂ r (Or.inl hr)
  have hH₂ : HR l n bV bLv bF bw bSum c₂ := hH.of fun r h1 h2 => by
    rw [hr₂ r (Or.inr (by omega)), hr₁ r (Or.inl (by omega))]
  have hm : ∀ a, a < bA → c₂.nmem a = c.nmem a := fun a ha => by
    rw [hf₂ a (Or.inl (by omega)), hf₁ a (Or.inl ha)]
  obtain ⟨c₃, t₃, e₃, ht₃, hfl1, hfl, hS₃, hr₃, hf₃, ho₃⟩ := wpass_exec (P := P) (bV := bV) (L := L)
    (lb := lb) ⟨l3, l4, l5, l6, by omega⟩ ⟨by omega, hW.2⟩ htot c₂ e₂.wb_right hR₂ hH₂
    (by rw [hr₂ 168 (Or.inr (by omega)), hr₁ 168 (Or.inl (by omega))]; exact h168)
    (fun v hv => by rw [hm _ (by omega)]; exact hL v hv)
    (fun v hv => by rw [hm _ (by omega)]; exact hF v hv)
    (fun v hv => by rw [hm _ (by omega)]; exact hw v hv)
    (fun g hg => ⟨hlb g hg, (hle g hg).trans hcc⟩)
    (fun x hx => by
      rw [hf₂ _ (Or.inr (by omega)), hf₁ _ (Or.inr (by omega))]; exact hz x hx)
  refine ⟨c₃, t₁ + (t₂ + t₃), .seq e₁ (.seq e₂ e₃), by omega, lb, hz0, hcls, hfl1, ?_, hS₃,
    fun g hg => ⟨by rw [hf₃ _ (Or.inl (by omega))]; exact hlb g hg, (hle g hg).trans hcc⟩,
    fun r hr => ?_, fun a ha => ?_, by rw [ho₃, ho₂, ho₁]⟩
  · rw [hfl]
    constructor
    · rintro ⟨x, -, hx⟩
      obtain ⟨u, hu, hLu, rfl⟩ := exists_of_sm hx
      exact ⟨u, hu, hLu, hx⟩
    · rintro ⟨v, hv, -, h⟩
      have hfk : fd v / 3 < k := by have := (hF v hv).2; omega
      exact ⟨_, (hle _ hfk).trans hcc, h⟩
  · rw [hr₃ r (by omega), hr₂ r (by omega), hr₁ r (by omega)]
  · rw [hf₃ a (by omega), hf₂ a (by omega), hf₁ a (by omega)]

end proofs

/-! ### The test is `Heavy` -/

section Bridge

open Map CycleSearch

variable {D P : Type*} [Fintype D] [DecidableEq D] [Fintype P] [DecidableEq P] {M : Map D P}
  {T₀ T : M.SpTree} {k n : ℕ} {cd : D ≃ Fin (3 * k)} {A Tm : ℕ → ℕ}
  (hC : Coded M T₀ k cd A Tm) (vi : P ≃ Fin n) {V L : ℕ → ℕ}
  (hV : ∀ x, V (cd x) = vi (M.vert x)) (hL : ∀ v, L (vi v) = T.height v)
include hC hV hL

omit [DecidableEq P] hC hV hL in
theorem sum_range_vi (vi : P ≃ Fin n) (g : ℕ → ℕ) : ∑ u ∈ range n, g u = ∑ v, g (vi v) := by
  rw [Fintype.sum_equiv vi (fun v => g (vi v)) (fun i : Fin n => g i) (fun _ => rfl)]
  exact (Fin.sum_univ_eq_sum_range g n).symm

/-- The flagged faces are the faces off `zone (T.low l)`. -/
theorem flagF_pos_iff (l : ℕ) (F : M.Face) :
    0 < flagF l V L (fi cd F) ↔ F ∉ M.zone (T.low l) := by
  rw [notMem_zone_iff]
  have hfk := hC.fi_lt F
  have hdart : ∀ j (hj : j < 3), L (V (3 * fi cd F + j)) = T.height (M.vert (cd.symm
      ⟨3 * fi cd F + j, by omega⟩)) ∧ M.face (cd.symm ⟨3 * fi cd F + j, by omega⟩) = F :=
    fun j hj => ⟨by rw [← hL, ← hV]; simp, hC.fi_inj (by rw [hC.fi_face]; simp; omega)⟩
  unfold flagF
  constructor
  · intro h d hd
    rw [mem_low, not_lt]
    split_ifs at h with hc
    · have hd3 : (cd d : ℕ) / 3 = fi cd F := by rw [← hC.fi_face, hd]
      have hj : (cd d : ℕ) % 3 < 3 := Nat.mod_lt _ (by omega)
      have e : 3 * fi cd F + (cd d : ℕ) % 3 = cd d := by omega
      have hc' : l ≤ L (V (3 * fi cd F + (cd d : ℕ) % 3)) := by
        rcases (by omega : (cd d : ℕ) % 3 = 0 ∨ (cd d : ℕ) % 3 = 1 ∨ (cd d : ℕ) % 3 = 2)
          with h0 | h0 | h0 <;> rw [h0]
        · exact hc.1
        · exact hc.2.1
        · exact hc.2.2
      rw [e, hV, hL] at hc'
      exact hc'
    · omega
  · intro h
    have hle : ∀ j < 3, l ≤ L (V (3 * fi cd F + j)) := fun j hj => by
      rw [(hdart j hj).1]
      have := h _ (hdart j hj).2
      rwa [mem_low, not_lt] at this
    rw [ite_eq_left ⟨by simpa using hle 0 (by omega), hle 1 (by omega), hle 2 (by omega)⟩]
    omega

/-- **The heavy test is `Heavy`.** For a triangulation coded by `cd`, its vertices numbered by
`vi`, the vertices `V` and levels `L` of a breadth-first tree `T` read through the numberings,
a dart `fdD v` at every vertex and labels `lb` of the components of the flagged faces (as
`hvy_exec` provides), the numeric test of `hvy_exec` at a level `l ≥ 1` holds if and only if
the level is heavy for the weights `wP v / Σ wP`. -/
theorem test_iff_heavy (hM : M.IsPlane) (hT : IsBFS T) (h3 : ∀ d : D, M.φ (M.φ (M.φ d)) = d)
    {l : ℕ} (hl : 1 ≤ l) (wP : P → ℕ) {fd w : ℕ → ℕ} (fdD : P → D)
    (hfdD : ∀ v, M.vert (fdD v) = v) (hfd : ∀ v, fd (vi v) = cd (fdD v))
    (hw : ∀ v, w (vi v) = wP v) {lb : ℕ → ℕ}
    (hlb : ∀ f < k, ∀ g < k, 0 < flagF l V L f → 0 < flagF l V L g →
      (lb f = lb g ↔ Relation.ReflTransGen (FA k A (flagF l V L)) f g)) :
    (∃ v < n, l < L v ∧ 2 * ∑ u ∈ range n, w u <
        3 * ∑ u ∈ range n, if l < L u ∧ lb (fd u / 3) = lb (fd v / 3) then w u else 0) ↔
      Heavy T (fun v => (wP v : ℝ) / ∑ u, (wP u : ℝ)) l := by
  classical
  rw [heavy_iff hM hT h3 hl wP hfdD]
  have hAv := flagF_pos_iff hC vi hV hL (T := T) l
  have hlab : ∀ u v : P, l < T.height u → l < T.height v →
      (lb (fd (vi u) / 3) = lb (fd (vi v) / 3) ↔
        M.face (fdD u) ∈ M.comp (T.low l) (M.face (fdD v))) := fun u v hu hv => by
    rw [hfd, hfd, ← hC.fi_face, ← hC.fi_face, eq_comm]
    exact label_eq_iff hC hAv hlb (notMem_zone_of_lt hT h3 hv (hfdD v))
      (notMem_zone_of_lt hT h3 hu (hfdD u))
  have hsum : ∀ v : P, l < T.height v →
      (∑ u ∈ range n, if l < L u ∧ lb (fd u / 3) = lb (fd (vi v) / 3) then w u else 0) =
        ∑ u ∈ univ.filter (fun u => l < T.height u ∧
          M.face (fdD u) ∈ M.comp (T.low l) (M.face (fdD v))), wP u := fun v hv => by
    rw [sum_range_vi vi, sum_filter]
    refine sum_congr rfl fun u _ => ?_
    rw [hL, hw]
    by_cases hu : l < T.height u
    · simp only [hu, true_and, hlab u v hu hv]
    · simp only [hu, false_and, ↓reduceIte]
  have htot : ∑ u ∈ range n, w u = ∑ u, wP u := by
    rw [sum_range_vi vi]; exact sum_congr rfl fun u _ => hw u
  constructor
  · rintro ⟨v, hv, hlv, h⟩
    obtain ⟨v', rfl⟩ : ∃ v', (vi v' : ℕ) = v := ⟨vi.symm ⟨v, hv⟩, by simp⟩
    rw [hL] at hlv
    refine ⟨v', hlv, ?_⟩
    rw [← hsum v' hlv, ← htot]
    exact h
  · rintro ⟨v, hlv, h⟩
    refine ⟨vi v, (vi v).2, by rw [hL]; exact hlv, ?_⟩
    rw [hsum v hlv, htot]
    exact h

/-- **The heavy test on the machine.** For a plane map `M` all of whose faces are triangles,
coded by `cd` in memory (reversals at `bR`, vertices at `bV`, read through a numbering `vi` of
the vertices), a breadth-first tree `T` whose levels are at `bLv`, a dart `fdD v` at every
vertex (at `bF`), natural weights `wP` (at `bw`, their total in `r168`) and a level `l ≥ 1`
(in `r160`), the program `hvy` ends within `101 k + 21 n + 11` steps with the flag `r169 = 1`
if and only if the level `l` is heavy (`PlanarSeparator.Map.Heavy`) for the weights
`wP v / Σ wP`. -/
theorem hvy_heavy {W : ℕ} {P' : Input} {bA bL bS bR l bV bLv bF bw bSum : ℕ}
    (hM : M.IsPlane) (hT : IsBFS T) (h3 : ∀ d : D, M.φ (M.φ (M.φ d)) = d) (hl : 1 ≤ l)
    (wP : P → ℕ) (fdD : P → D) (hfdD : ∀ v, M.vert (fdD v) = v) {fd w : ℕ → ℕ}
    (hfd : ∀ v, fd (vi v) = cd (fdD v)) (hw : ∀ v, w (vi v) = wP v)
    (hlay : bR + 3 * k ≤ bA ∧ bV + 3 * k ≤ bA ∧ bLv + n ≤ bA ∧ bF + n ≤ bA ∧ bw + n ≤ bA ∧
      bA + k ≤ bL ∧ bL + k ≤ bS ∧ bS + k ≤ bSum)
    (hW : bSum + 3 * k + 3 * l + n + 1 ≤ W ∧ 3 * ∑ v, wP v ≤ W)
    (c : Config) (hc : WordsBounded W c) (hR : CR k bA bL bS bR c)
    (hH : HR l n bV bLv bF bw bSum c) (h168 : c.nreg 168 = ∑ v, wP v)
    (hAm : ∀ x < 3 * k, c.nmem (bR + x) = A x) (hVm : ∀ x < 3 * k, c.nmem (bV + x) = V x)
    (hLm : ∀ v < n, c.nmem (bLv + v) = L v) (hFm : ∀ v < n, c.nmem (bF + v) = fd v)
    (hwm : ∀ v < n, c.nmem (bw + v) = w v) (hz : ∀ x ≤ k, c.nmem (bSum + x) = 0) :
    ∃ c' t, Exec P' W hvy c c' t ∧ t ≤ 101 * k + 21 * n + 11 ∧ c'.nreg 169 ≤ 1 ∧
      (c'.nreg 169 = 1 ↔ Heavy T (fun v => (wP v : ℝ) / ∑ u, (wP u : ℝ)) l) ∧
      (∀ r, r < 150 ∨ (160 ≤ r ∧ r < 169) ∨ 180 ≤ r → c'.nreg r = c.nreg r) ∧
      (∀ a, a < bA ∨ bSum + k + 1 ≤ a → c'.nmem a = c.nmem a) ∧ c'.output = c.output := by
  have htot : ∑ u ∈ range n, w u = ∑ v, wP v := by
    rw [sum_range_vi vi]; exact sum_congr rfl fun u _ => hw u
  have hVn : ∀ x < 3 * k, c.nmem (bV + x) = V x ∧ V x < n := fun x hx => by
    refine ⟨hVm x hx, ?_⟩
    have : V x = vi (M.vert (cd.symm ⟨x, hx⟩)) := by rw [← hV]; simp
    rw [this]; exact (vi _).2
  have hFk : ∀ v < n, c.nmem (bF + v) = fd v ∧ fd v < 3 * k := fun v hv => by
    refine ⟨hFm v hv, ?_⟩
    have : fd v = cd (fdD (vi.symm ⟨v, hv⟩)) := by rw [← hfd]; simp
    rw [this]; exact (cd _).2
  obtain ⟨c', t, e, ht, lb, -, hcls, hfl1, hfl, -, -, hr, hf, ho⟩ := hvy_exec (P := P') (L := L)
    (revOk hC) hlay hW htot c hc hR hH h168 hAm hVn hLm hFk hwm hz
  refine ⟨c', t, e, ht, hfl1, ?_, hr, hf, ho⟩
  rw [hfl, ← test_iff_heavy hC vi hV hL hM hT h3 hl wP fdD hfdD hfd hw hcls, htot]

end Bridge

end MillerProg

end PlanarSeparator
