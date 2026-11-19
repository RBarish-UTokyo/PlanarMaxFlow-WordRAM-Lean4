module

public import PlanarSeparator.Machine.MillerBFS
public import PlanarSeparator.MillerInner

/-!
# Miller's separator on the machine: the inner region

Step 6 of the plan in `PlanarSeparator/Machine/Miller.lean`, at a heavy level `l₀ ≥ 1`. After
the heavy test `hvy` at `l₀` (`PlanarSeparator/Machine/MillerTest.lean`), which leaves the labels
`lb` of the components at `bL` and the weights `S` of their strict insides at `bSum`:

* `hpass` finds a vertex `vH` of level `> l₀` whose label `h₀` weighs more than `2/3` of the
  total (`r238 = vH`, `r237 = h₀`);
* `xpass` finds a dart `x₀` leaving the component `H` of label `h₀` (`lb (x₀ / 3) = h₀ ≠
  lb (A x₀ / 3)`, in `r239`), and `c₀ = V x₀` (in `r240`);
* `ppass` overwrites the parent dart at the head `V (A x)` of every dart `x` leaving `H`, other
  than `c₀`, by `A x` (at `bPr`).

By `PlanarSeparator.Map.inner_explicit`, the parent darts are then those of the tree `T₁` of an
inner region (`PlanarSeparator.Map.Inner`) for `H` with `c₀` the vertex of `x₀`
(`iprog_inner`).

Registers: those of `hvy`, and `r215 = bPr`; the passes write `r230 … r244`.
-/

@[expose] public section

namespace PlanarSeparator

namespace MillerProg

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs Finset

/-! ### The programs -/

/-- **One vertex** `r230 = v`: if its level is `> l` and its label `r234` weighs more than `2/3`
of the total, record the label (`r237`) and the vertex (`r238`). -/
def hbody : Stmt :=
  .seq (block [.addN 231 163 230, .loadN 232 231])
    (.seq (.ifLtN 160 232
        (.seq (block [.addN 231 164 230, .loadN 233 231, .divN 233 233 142, .addN 231 145 233,
            .loadN 234 231, .addN 231 166 234, .loadN 235 231, .mulN 235 235 142,
            .addN 236 168 168])
          (.ifLtN 236 235 (block [.copyN 237 234, .copyN 238 230]) .skip))
        .skip)
      (.instr (.addN 230 230 141)))

/-- **A heavy label.** -/
def hpass : Stmt := .seq (.instr (.copyN 230 140)) (.whileLtN 230 161 hbody)

/-- The test of the dart `r230 = x`: `r233 = A x`, `r235 = |lb (x / 3) - h₀|`,
`r236 = |lb (A x / 3) - h₀|`. -/
def ltest : List Instr :=
  [.divN 231 230 142, .addN 231 145 231, .loadN 232 231, .addN 231 147 230, .loadN 233 231,
    .divN 231 233 142, .addN 231 145 231, .loadN 234 231, .subN 235 232 237, .subN 236 237 232,
    .addN 235 235 236, .subN 236 234 237, .subN 231 237 234, .addN 236 236 231]

/-- **One dart** `r230 = x`: if it leaves `H`, record it. -/
def xbody : Stmt :=
  .seq (block ltest)
    (.seq (.ifLtN 235 141 (.ifLtN 140 236 (.instr (.copyN 239 230)) .skip) .skip)
      (.instr (.addN 230 230 141)))

/-- **A dart leaving `H`**, and its vertex `c₀` in `r240`. -/
def xpass : Stmt :=
  .seq (block [.copyN 230 140, .mulN 244 143 142, .copyN 239 140]) (.seq (.whileLtN 230 244 xbody)
    (block [.addN 231 162 239, .loadN 240 231]))

/-- The head `r241 = V (A x)` of a dart leaving `H`: unless it is `c₀`, its parent dart becomes
`A x`. -/
def pact : Stmt :=
  .seq (block [.addN 231 162 233, .loadN 241 231, .subN 242 241 240, .subN 243 240 241,
      .addN 242 242 243])
    (.ifLtN 140 242 (block [.addN 231 215 241, .storeN 231 233]) .skip)

/-- **One dart** `r230 = x`: if it leaves `H`, redirect at its head. -/
def pbody : Stmt :=
  .seq (block ltest)
    (.seq (.ifLtN 235 141 (.ifLtN 140 236 pact .skip) .skip) (.instr (.addN 230 230 141)))

/-- **The redirected parent darts.** -/
def ppass : Stmt := .seq (.instr (.copyN 230 140)) (.whileLtN 230 244 pbody)

/-- **The inner region** at the level `r160`: the heavy test, a heavy label, a dart leaving its
component, and the redirected parent darts. -/
def iprog : Stmt := .seq zpass (.seq hvy (.seq hpass (.seq xpass ppass)))

/-- A dart leaving the component of label `h`. -/
def Lv (lb A : ℕ → ℕ) (h x : ℕ) : Prop := lb (x / 3) = h ∧ lb (A x / 3) ≠ h

section proofs

variable {k : ℕ} {bA bL bS bR : ℕ} {W : ℕ} {P : Input}
  {l n bV bLv bF bw bSum : ℕ} {L : ℕ → ℕ}

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
set_option linter.unusedTactic false in
theorem hpass_exec {fd lb S : ℕ → ℕ} {tot : ℕ}
    (hlay : bLv + n ≤ bA ∧ bF + n ≤ bA ∧ bA + k ≤ bL ∧ bL + k ≤ bSum)
    (hW : bSum + k + 1 + n ≤ W ∧ 3 * tot ≤ W) (c : Config) (hc : WordsBounded W c)
    (hR : CR k bA bL bS bR c) (hH : HR l n bV bLv bF bw bSum c) (h168 : c.nreg 168 = tot)
    (hL : ∀ v < n, c.nmem (bLv + v) = L v)
    (hF : ∀ v < n, c.nmem (bF + v) = fd v ∧ fd v < 3 * k)
    (hlb : ∀ g < k, c.nmem (bL + g) = lb g ∧ lb g ≤ k)
    (hS : ∀ x ≤ k, c.nmem (bSum + x) = S x ∧ S x ≤ tot) :
    ∃ c' t, Exec P W hpass c c' t ∧ t ≤ 18 * n + 3 ∧
      ((∃ v < n, l < L v ∧ 2 * tot < 3 * S (lb (fd v / 3))) →
        c'.nreg 238 < n ∧ l < L (c'.nreg 238) ∧ 2 * tot < 3 * S (lb (fd (c'.nreg 238) / 3)) ∧
        c'.nreg 237 = lb (fd (c'.nreg 238) / 3)) ∧
      (∀ r, r < 230 ∨ 239 ≤ r → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem ∧
      c'.output = c.output := by
  obtain ⟨r140, r141, r142, r143, r144, r145, r146, r147⟩ := hR
  obtain ⟨r160, r161, r162, r163, r164, r165, r166⟩ := hH
  let Q : ℕ → Prop := fun v => l < L v ∧ 2 * tot < 3 * S (lb (fd v / 3))
  let I : ℕ → Config → Prop := fun i c' => WordsBounded W c' ∧ c'.nreg 230 = i ∧
    c'.nreg 161 = n ∧ i ≤ n ∧
    ((∃ v < i, Q v) → c'.nreg 238 < i ∧ Q (c'.nreg 238) ∧
      c'.nreg 237 = lb (fd (c'.nreg 238) / 3)) ∧
    (∀ r, r < 230 ∨ 239 ≤ r → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem ∧ c'.output = c.output
  have e₁ := Exec.copyN (P := P) hc 230 140
  obtain ⟨c', t, e, hI, ht⟩ := Exec.forN (P := P) (W := W) (ri := 230) (rN := 161) (N := n)
    (lo := 0) (B := 16) (body := hbody) I (fun i c' h => ⟨h.1, h.2.1, h.2.2.1⟩)
    (fun i c₁ ⟨hw₁, h230, h161, hin, hP, hr, hm, ho⟩ hi => by
      have g : ∀ r, r < 230 → c₁.nreg r = c.nreg r := fun r hr' => hr r (Or.inl hr')
      have g160 : c₁.nreg 160 = l := by rw [g 160 (by omega)]; exact r160
      have g163 : c₁.nreg 163 = bLv := by rw [g 163 (by omega)]; exact r163
      have g164 : c₁.nreg 164 = bF := by rw [g 164 (by omega)]; exact r164
      have g166 : c₁.nreg 166 = bSum := by rw [g 166 (by omega)]; exact r166
      have g168 : c₁.nreg 168 = tot := by rw [g 168 (by omega)]; exact h168
      have g141 : c₁.nreg 141 = 1 := by rw [g 141 (by omega)]; exact r141
      have g142 : c₁.nreg 142 = 3 := by rw [g 142 (by omega)]; exact r142
      have g145 : c₁.nreg 145 = bL := by rw [g 145 (by omega)]; exact r145
      have mL : c₁.nmem (bLv + i) = L i := by rw [hm]; exact hL i hi
      have mF : c₁.nmem (bF + i) = fd i := by rw [hm]; exact (hF i hi).1
      have hfk : fd i / 3 < k := by have := (hF i hi).2; omega
      have mb : c₁.nmem (bL + fd i / 3) = lb (fd i / 3) := by rw [hm]; exact (hlb _ hfk).1
      have hlbk := (hlb _ hfk).2
      have mS : c₁.nmem (bSum + lb (fd i / 3)) = S (lb (fd i / 3)) := by
        rw [hm]; exact (hS _ hlbk).1
      have hSle := (hS _ hlbk).2
      unfold hbody
      refine spec_seq ?_
      exec_block
      · config_simp; rw [g163, h230]; omega
      rename_i hwb
      simp only [g163, h230, mL] at hwb ⊢
      refine spec_seq ?_
      have hstep : ∀ c₂ : Config, WordsBounded W c₂ → c₂.nreg 230 = i →
          (∀ r, r < 230 ∨ 239 ≤ r → c₂.nreg r = c.nreg r) → c₂.nmem = c.nmem →
          c₂.output = c.output → c₂.nreg 161 = n →
          ((∃ v < i + 1, Q v) → c₂.nreg 238 < i + 1 ∧ Q (c₂.nreg 238) ∧
            c₂.nreg 237 = lb (fd (c₂.nreg 238) / 3)) →
          ∃ c' k, Exec P W (.instr (.addN 230 230 141)) c₂ c' k ∧ I (i + 1) c' ∧ k ≤ 1 := by
        intro c₂ hw₂ f230 fr fm fo f161 fP
        have f141 : c₂.nreg 141 = 1 := by rw [fr 141 (by omega)]; exact r141
        have ea := Exec.addN (P := P) hw₂ 230 230 141 (by rw [f230, f141]; omega)
        refine ⟨_, 1, ea, ⟨ea.wb_right,
            by config_simp; rw [f230, f141], by config_simp; exact f161, by omega, ?_,
            fun r hr' => by config_simp; simp only [upd_apply]; split_ifs <;>
              first | omega | exact fr r hr',
            by config_simp; exact fm, by config_simp; exact fo⟩, le_rfl⟩
        config_simp
        intro hex
        obtain ⟨a1, a2, a3⟩ := fP hex
        exact ⟨a1, a2, a3⟩
      by_cases hli : l < L i
      · refine spec_ifLtN_true (by config_simp; rw [g160]; exact hli) ?_
        refine spec_seq ?_
        exec_block
        all_goals try (config_simp; (try simp only [g164, h230, mF, g142, g145, mb, g166,
                                                     mS, g168]); omega)
        rename_i hwc
        simp only [g164, h230, mF, g142, g145, mb, g166, mS, g168] at hwc ⊢
        by_cases hq : 2 * tot < 3 * S (lb (fd i / 3))
        · refine spec_ifLtN_true (by config_simp; omega) ?_
          exec_block
          rename_i hwd
          obtain ⟨c'', k'', e'', hI'', hk''⟩ := hstep _ hwd (by config_simp; exact h230)
            (fun r hr' => by config_simp; simp only [upd_apply]; split_ifs <;>
              first | omega | exact hr r hr') (by config_simp; exact hm)
            (by config_simp; exact ho) (by config_simp; exact h161)
            (fun _ => by config_simp; simp only [h230]; exact ⟨by omega, ⟨hli, hq⟩, trivial⟩)
          exact ⟨c'', k'', e'', hI'', by omega⟩
        · refine spec_ifLtN_false (by config_simp; omega) ?_
          refine spec_skip ‹_› ?_
          obtain ⟨c'', k'', e'', hI'', hk''⟩ := hstep _ hwc (by config_simp; exact h230)
            (fun r hr' => by config_simp; simp only [upd_apply]; split_ifs <;>
              first | omega | exact hr r hr') (by config_simp; exact hm)
            (by config_simp; exact ho) (by config_simp; exact h161)
            (fun ⟨v, hv, hQ⟩ => by
              config_simp
              rcases Nat.lt_succ_iff_lt_or_eq.1 hv with hv | rfl
              · obtain ⟨a1, a2, a3⟩ := hP ⟨v, hv, hQ⟩; exact ⟨by omega, a2, a3⟩
              · exact absurd hQ.2 hq)
          exact ⟨c'', k'', e'', hI'', by omega⟩
      · refine spec_ifLtN_false (by config_simp; rw [g160]; exact hli) ?_
        refine spec_skip ‹_› ?_
        obtain ⟨c'', k'', e'', hI'', hk''⟩ := hstep _ hwb (by config_simp; exact h230)
          (fun r hr' => by config_simp; simp only [upd_apply]; split_ifs <;>
            first | omega | exact hr r hr') (by config_simp; exact hm)
          (by config_simp; exact ho) (by config_simp; exact h161)
          (fun ⟨v, hv, hQ⟩ => by
            config_simp
            rcases Nat.lt_succ_iff_lt_or_eq.1 hv with hv | rfl
            · obtain ⟨a1, a2, a3⟩ := hP ⟨v, hv, hQ⟩; exact ⟨by omega, a2, a3⟩
            · exact absurd hQ.1 hli)
        exact ⟨c'', k'', e'', hI'', by omega⟩)
    (by omega) ⟨e₁.wb_right, by config_simp; exact r140, by config_simp; exact r161, by omega,
      fun ⟨v, hv, _⟩ => absurd hv (by omega), fun r hr => by
        show upd c.nreg 230 (c.nreg 140) r = c.nreg r
        simp only [upd_apply]; split_ifs <;> omega, rfl, rfl⟩
  obtain ⟨-, -, -, -, hP', hr', hm', ho'⟩ := hI
  exact ⟨c', 1 + t, .seq e₁ e, by omega, fun h => by
    obtain ⟨a1, ⟨a2, a3⟩, a4⟩ := hP' h; exact ⟨a1, a2, a3, a4⟩, hr', hm', ho'⟩

set_option linter.unusedSimpArgs false in
set_option linter.unusedTactic false in
/-- The test of a dart. -/
theorem ltest_exec {A lb : ℕ → ℕ} {h x : ℕ} (hW : bL + k ≤ W ∧ bR + 3 * k ≤ W) (c : Config)
    (hc : WordsBounded W c) (h142 : c.nreg 142 = 3) (h145 : c.nreg 145 = bL)
    (h147 : c.nreg 147 = bR) (h237 : c.nreg 237 = h) (h230 : c.nreg 230 = x) (hx : x < 3 * k)
    (mA : c.nmem (bR + x) = A x) (hAx : A x < 3 * k) (m1 : c.nmem (bL + x / 3) = lb (x / 3))
    (m2 : c.nmem (bL + A x / 3) = lb (A x / 3)) :
    ∃ c' t, Exec P W (block ltest) c c' t ∧ t = 14 ∧ c'.nreg 233 = A x ∧
      (c'.nreg 235 < 1 ↔ lb (x / 3) = h) ∧ (0 < c'.nreg 236 ↔ lb (A x / 3) ≠ h) ∧
      (∀ r, r < 231 ∨ 237 ≤ r → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem ∧
      c'.output = c.output := by
  have hb1 := hc.2 (bL + x / 3)
  have hb2 := hc.2 (bL + A x / 3)
  have hh := hc.1 237
  rw [m1] at hb1; rw [m2] at hb2; rw [h237] at hh
  unfold ltest
  exec_block
  all_goals try (config_simp; (try simp only [h142, h145, h147, h230, mA, m1, m2, h237]); omega)
  rename_i hwb
  simp only [h142, h145, h147, h230, mA, m1, m2, h237] at hwb ⊢
  refine ⟨trivial, by config_simp, by config_simp; omega, by config_simp; omega, fun r hr => ?_,
    by config_simp, by config_simp⟩
  config_simp; simp only [upd_apply]; split_ifs <;> omega

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
set_option linter.unusedTactic false in
/-- **A dart leaving `H`.** -/
theorem xpass_exec {A lb V : ℕ → ℕ} {h : ℕ} (hk : 0 < k)
    (hW : bL + k ≤ W ∧ bR + 3 * k ≤ W ∧ bV + 3 * k ≤ W) (c : Config) (hc : WordsBounded W c)
    (hR : CR k bA bL bS bR c) (h162 : c.nreg 162 = bV) (h237 : c.nreg 237 = h)
    (hA : ∀ x < 3 * k, c.nmem (bR + x) = A x ∧ A x < 3 * k)
    (hlb : ∀ g < k, c.nmem (bL + g) = lb g) (hV : ∀ x < 3 * k, c.nmem (bV + x) = V x) :
    ∃ c' t, Exec P W xpass c c' t ∧ t ≤ 60 * k + 7 ∧
      ((∃ x < 3 * k, Lv lb A h x) → Lv lb A h (c'.nreg 239)) ∧ c'.nreg 239 < 3 * k ∧
      c'.nreg 240 = V (c'.nreg 239) ∧ c'.nreg 244 = 3 * k ∧
      (∀ r, r < 230 ∨ (237 ≤ r ∧ r < 239) ∨ 245 ≤ r → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.output = c.output := by
  obtain ⟨r140, r141, r142, r143, r144, r145, r146, r147⟩ := hR
  let I : ℕ → Config → Prop := fun i c' => WordsBounded W c' ∧ c'.nreg 230 = i ∧
    c'.nreg 244 = 3 * k ∧ i ≤ 3 * k ∧ c'.nreg 239 < 3 * k ∧
    ((∃ x < i, Lv lb A h x) → Lv lb A h (c'.nreg 239)) ∧
    (∀ r, r < 230 ∨ (237 ≤ r ∧ r < 239) ∨ 245 ≤ r → c'.nreg r = c.nreg r) ∧
    c'.nmem = c.nmem ∧ c'.output = c.output
  obtain ⟨c₁, k₁, e₁, hI₁, rfl⟩ : ∃ c₁ k₁, Exec P W (block [.copyN 230 140, .mulN 244 143 142,
      .copyN 239 140]) c c₁ k₁ ∧ I 0 c₁ ∧ k₁ = 3 := by
    exec_block
    · config_simp; rw [r143, r142]; omega
    refine ⟨⟨‹_›, by config_simp; exact r140, by config_simp; rw [r143, r142]; ring, by omega,
      by config_simp; omega, fun ⟨x, hx, _⟩ => absurd hx (by omega), fun r hr => by
        config_simp; simp only [upd_apply]; split_ifs <;> omega, rfl, rfl⟩, rfl⟩
  obtain ⟨c₂, t, e, hI, ht⟩ := Exec.forN (P := P) (W := W) (ri := 230) (rN := 244)
    (N := 3 * k) (lo := 0) (B := 18) (body := xbody) I (fun i c' h => ⟨h.1, h.2.1, h.2.2.1⟩)
    (fun i c₁ ⟨hw₁, h230, h244, hin, h239, hP, hr, hm, ho⟩ hi => by
      have g : ∀ r, r < 230 → c₁.nreg r = c.nreg r := fun r hr' => hr r (Or.inl hr')
      have g140 : c₁.nreg 140 = 0 := by rw [g 140 (by omega)]; exact r140
      have g141 : c₁.nreg 141 = 1 := by rw [g 141 (by omega)]; exact r141
      have g142 : c₁.nreg 142 = 3 := by rw [g 142 (by omega)]; exact r142
      have g145 : c₁.nreg 145 = bL := by rw [g 145 (by omega)]; exact r145
      have g147 : c₁.nreg 147 = bR := by rw [g 147 (by omega)]; exact r147
      have g237 : c₁.nreg 237 = h := by rw [hr 237 (by omega)]; exact h237
      obtain ⟨mA, hAi⟩ := hA i hi
      obtain ⟨c₂, t₂, e₂, rfl, f233, f235, f236, fr, fm, fo⟩ := ltest_exec (P := P) (lb := lb)
        ⟨hW.1, hW.2.1⟩ c₁ hw₁ g142 g145 g147 g237 h230 hi (by rw [hm]; exact mA) hAi
        (by rw [hm]; exact hlb _ (by omega)) (by rw [hm]; exact hlb _ (by omega))
      have hw₂ := e₂.wb_right
      have f230 : c₂.nreg 230 = i := (fr 230 (by omega)).trans h230
      have f140 : c₂.nreg 140 = 0 := (fr 140 (by omega)).trans g140
      have f141 : c₂.nreg 141 = 1 := (fr 141 (by omega)).trans g141
      have f239 : c₂.nreg 239 = c₁.nreg 239 := fr 239 (by omega)
      have f244 : c₂.nreg 244 = 3 * k := (fr 244 (by omega)).trans h244
      have hstep : ∀ c₃ : Config, WordsBounded W c₃ → c₃.nreg 230 = i →
          (∀ r, r < 230 ∨ (237 ≤ r ∧ r < 239) ∨ 240 ≤ r → c₃.nreg r = c₂.nreg r) →
          c₃.nmem = c.nmem → c₃.output = c.output → c₃.nreg 239 < 3 * k →
          ((∃ x < i + 1, Lv lb A h x) → Lv lb A h (c₃.nreg 239)) →
          ∃ c' k, Exec P W (.instr (.addN 230 230 141)) c₃ c' k ∧ I (i + 1) c' ∧ k ≤ 1 := by
        intro c₃ hw₃ e230 er em eo e239 eP
        have e141 : c₃.nreg 141 = 1 := (er 141 (by omega)).trans f141
        have ea := Exec.addN (P := P) hw₃ 230 230 141 (by rw [e230, e141]; omega)
        refine ⟨_, 1, ea, ⟨ea.wb_right, by config_simp; rw [e230, e141], ?_, by omega,
          by config_simp; exact e239, by config_simp; exact eP, fun r hr' => ?_,
          by config_simp; exact em, by config_simp; exact eo⟩, le_rfl⟩
        · config_simp; rw [er 244 (by omega), f244]
        · config_simp; simp only [upd_apply]
          split_ifs with h'
          · omega
          · rw [er r (by omega), fr r (by omega)]; exact hr r hr'
      unfold xbody
      refine spec_seq ⟨c₂, 14, e₂, ?_⟩
      refine spec_seq ?_
      by_cases hl1 : lb (i / 3) = h
      · refine spec_ifLtN_true (by rw [f141]; exact f235.2 hl1) ?_
        by_cases hl2 : lb (A i / 3) ≠ h
        · refine spec_ifLtN_true (by rw [f140]; exact f236.2 hl2) ?_
          refine spec_instr (Exec.copyN hw₂ 239 230) fun hw₃ => ?_
          obtain ⟨c', k', e', hI', hk'⟩ := hstep _ hw₃ (by config_simp; exact f230)
            (fun r hr' => by config_simp; simp only [upd_apply]; split_ifs <;> omega)
            (by config_simp; rw [fm, hm]) (by config_simp; rw [fo, ho])
            (by config_simp; rw [f230]; exact hi)
            (fun _ => by config_simp; rw [f230]; exact ⟨hl1, hl2⟩)
          exact ⟨c', k', e', hI', by omega⟩
        · refine spec_ifLtN_false (by rw [f140]; exact fun h' => hl2 (f236.1 h')) ?_
          refine spec_skip hw₂ ?_
          obtain ⟨c', k', e', hI', hk'⟩ := hstep _ hw₂ f230 (fun r _ => rfl) (by rw [fm, hm])
            (by rw [fo, ho]) (by rw [f239]; exact h239) (fun ⟨x, hx, hL⟩ => by
              rw [f239]
              rcases Nat.lt_succ_iff_lt_or_eq.1 hx with hx | rfl
              · exact hP ⟨x, hx, hL⟩
              · exact absurd hL.2 hl2)
          exact ⟨c', k', e', hI', by omega⟩
      · refine spec_ifLtN_false (by rw [f141]; exact fun h' => hl1 (f235.1 h')) ?_
        refine spec_skip hw₂ ?_
        obtain ⟨c', k', e', hI', hk'⟩ := hstep _ hw₂ f230 (fun r _ => rfl) (by rw [fm, hm])
          (by rw [fo, ho]) (by rw [f239]; exact h239) (fun ⟨x, hx, hL⟩ => by
            rw [f239]
            rcases Nat.lt_succ_iff_lt_or_eq.1 hx with hx | rfl
            · exact hP ⟨x, hx, hL⟩
            · exact absurd hL.1 hl1)
        exact ⟨c', k', e', hI', by omega⟩)
    (by omega) hI₁
  obtain ⟨hw₂, -, h244', -, h239', hP', hr', hm', ho'⟩ := hI
  have g162 : c₂.nreg 162 = bV := (hr' 162 (by omega)).trans h162
  have hb : c₂.nreg 162 + c₂.nreg 239 ≤ W := by rw [g162]; omega
  have ea := Exec.addN (P := P) hw₂ 231 162 239 hb
  have el := Exec.loadN (P := P) ea.wb_right 240 231
  refine ⟨_, 3 + (t + 2), .seq e₁ (.seq e (Exec.block_cons ea (Exec.block_cons el
    (Exec.block_nil el.wb_right)))), by omega, ?_, ?_, ?_, ?_, fun r hr => ?_, ?_, ?_⟩
  all_goals config_simp
  · exact hP'
  · exact h239'
  · rw [g162, hm']; exact hV _ h239'
  · exact h244'
  · simp only [upd_apply]; split_ifs <;> first | omega | exact hr' r hr
  · exact hm'
  · exact ho'

/-- The cells `b + v` of the heads `v = hd x` of the darts `x < i` with `Q x` hold `A x` for one
such dart; the others are unchanged from `m₀`. -/
def PInv (n b : ℕ) (Q : ℕ → Prop) (hd A m₀ : ℕ → ℕ) (i : ℕ) (m : ℕ → ℕ) : Prop :=
  ∀ v < n, ((∃ x < i, Q x ∧ hd x = v) → ∃ x < i, Q x ∧ hd x = v ∧ m (b + v) = A x) ∧
    ((¬ ∃ x < i, Q x ∧ hd x = v) → m (b + v) = m₀ (b + v))

theorem PInv.store {n b : ℕ} {Q : ℕ → Prop} {hd A m₀ m : ℕ → ℕ} {i : ℕ}
    (h : PInv n b Q hd A m₀ i m) (hQ : Q i) (hh : hd i < n) :
    PInv n b Q hd A m₀ (i + 1) (upd m (b + hd i) (A i)) := by
  intro v hv
  by_cases e : v = hd i
  · subst e
    refine ⟨fun _ => ⟨i, by omega, hQ, rfl, by rw [upd_same]⟩, fun hn => ?_⟩
    exact absurd ⟨i, by omega, hQ, rfl⟩ hn
  · rw [upd_other _ _ _ (by omega)]
    have hiff : (∃ x < i + 1, Q x ∧ hd x = v) ↔ ∃ x < i, Q x ∧ hd x = v := by
      constructor
      · rintro ⟨x, hx, hq, rfl⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hx with hx | rfl
        · exact ⟨x, hx, hq, rfl⟩
        · exact absurd rfl e
      · rintro ⟨x, hx, hq, he⟩; exact ⟨x, by omega, hq, he⟩
    rw [hiff]
    refine ⟨fun hex => ?_, (h v hv).2⟩
    obtain ⟨x, hx, hq, he, hm⟩ := (h v hv).1 hex
    exact ⟨x, by omega, hq, he, hm⟩

theorem PInv.skip {n b : ℕ} {Q : ℕ → Prop} {hd A m₀ m : ℕ → ℕ} {i : ℕ}
    (h : PInv n b Q hd A m₀ i m) (hQ : ¬ Q i) : PInv n b Q hd A m₀ (i + 1) m := by
  intro v hv
  have hiff : (∃ x < i + 1, Q x ∧ hd x = v) ↔ ∃ x < i, Q x ∧ hd x = v := by
    constructor
    · rintro ⟨x, hx, hq, he⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hx with hx | rfl
      · exact ⟨x, hx, hq, he⟩
      · exact absurd hq hQ
    · rintro ⟨x, hx, hq, he⟩; exact ⟨x, by omega, hq, he⟩
  rw [hiff]
  refine ⟨fun hex => ?_, (h v hv).2⟩
  obtain ⟨x, hx, hq, he, hm⟩ := (h v hv).1 hex
  exact ⟨x, by omega, hq, he, hm⟩

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
set_option linter.unusedTactic false in
/-- **The redirected parent darts.** -/
theorem ppass_exec {A lb V : ℕ → ℕ} {h c0 bPr : ℕ}
    (hlay : bR + 3 * k ≤ bPr ∧ bV + 3 * k ≤ bPr ∧ bPr + n ≤ bL) (hW : bL + k ≤ W)
    (c : Config) (hc : WordsBounded W c)
    (hR : CR k bA bL bS bR c) (h162 : c.nreg 162 = bV) (h215 : c.nreg 215 = bPr)
    (h237 : c.nreg 237 = h) (h240 : c.nreg 240 = c0) (h244 : c.nreg 244 = 3 * k)
    (hA : ∀ x < 3 * k, c.nmem (bR + x) = A x ∧ A x < 3 * k)
    (hlb : ∀ g < k, c.nmem (bL + g) = lb g) (hV : ∀ x < 3 * k, c.nmem (bV + x) = V x ∧ V x < n) :
    ∃ c' t, Exec P W ppass c c' t ∧ t ≤ 81 * k + 3 ∧
      PInv n bPr (fun x => Lv lb A h x ∧ V (A x) ≠ c0) (fun x => V (A x)) A c.nmem (3 * k)
        c'.nmem ∧
      (∀ a, a < bPr ∨ bPr + n ≤ a → c'.nmem a = c.nmem a) ∧
      (∀ r, r < 230 ∨ (237 ≤ r ∧ r < 241) ∨ 244 ≤ r → c'.nreg r = c.nreg r) ∧
      c'.output = c.output := by
  obtain ⟨r140, r141, r142, r143, r144, r145, r146, r147⟩ := hR
  set Q : ℕ → Prop := fun x => Lv lb A h x ∧ V (A x) ≠ c0
  let I : ℕ → Config → Prop := fun i c' => WordsBounded W c' ∧ c'.nreg 230 = i ∧
    c'.nreg 244 = 3 * k ∧ i ≤ 3 * k ∧
    PInv n bPr Q (fun x => V (A x)) A c.nmem i c'.nmem ∧
    (∀ a, a < bPr ∨ bPr + n ≤ a → c'.nmem a = c.nmem a) ∧
    (∀ r, r < 230 ∨ (237 ≤ r ∧ r < 241) ∨ 244 ≤ r → c'.nreg r = c.nreg r) ∧
    c'.output = c.output
  have e₁ := Exec.copyN (P := P) hc 230 140
  obtain ⟨c₂, t, e, hI, ht⟩ := Exec.forN (P := P) (W := W) (ri := 230) (rN := 244)
    (N := 3 * k) (lo := 0) (B := 25) (body := pbody) I (fun i c' h => ⟨h.1, h.2.1, h.2.2.1⟩)
    (fun i c₁ ⟨hw₁, h230, h244', hin, hP, hf, hr, ho⟩ hi => by
      have g : ∀ r, r < 230 → c₁.nreg r = c.nreg r := fun r hr' => hr r (Or.inl hr')
      have g140 : c₁.nreg 140 = 0 := by rw [g 140 (by omega)]; exact r140
      have g141 : c₁.nreg 141 = 1 := by rw [g 141 (by omega)]; exact r141
      have g142 : c₁.nreg 142 = 3 := by rw [g 142 (by omega)]; exact r142
      have g145 : c₁.nreg 145 = bL := by rw [g 145 (by omega)]; exact r145
      have g147 : c₁.nreg 147 = bR := by rw [g 147 (by omega)]; exact r147
      have g162 : c₁.nreg 162 = bV := by rw [g 162 (by omega)]; exact h162
      have g215 : c₁.nreg 215 = bPr := by rw [g 215 (by omega)]; exact h215
      have g237 : c₁.nreg 237 = h := by rw [hr 237 (by omega)]; exact h237
      have g240 : c₁.nreg 240 = c0 := by rw [hr 240 (by omega)]; exact h240
      obtain ⟨mA, hAi⟩ := hA i hi
      obtain ⟨c₂, t₂, e₂, rfl, f233, f235, f236, fr, fm, fo⟩ := ltest_exec (P := P) (lb := lb)
        ⟨hW, by omega⟩ c₁ hw₁ g142 g145 g147 g237 h230 hi
        (by rw [hf _ (Or.inl (by omega))]; exact mA) hAi
        (by rw [hf _ (Or.inr (by omega))]; exact hlb _ (by omega))
        (by rw [hf _ (Or.inr (by omega))]; exact hlb _ (by omega))
      have hw₂ := e₂.wb_right
      have f230 : c₂.nreg 230 = i := (fr 230 (by omega)).trans h230
      have f140 : c₂.nreg 140 = 0 := (fr 140 (by omega)).trans g140
      have f141 : c₂.nreg 141 = 1 := (fr 141 (by omega)).trans g141
      have hstep : ∀ c₃ : Config, WordsBounded W c₃ → c₃.nreg 230 = i →
          (∀ r, r < 230 ∨ (237 ≤ r ∧ r < 241) ∨ 244 ≤ r → c₃.nreg r = c₂.nreg r) →
          PInv n bPr Q (fun x => V (A x)) A c.nmem (i + 1) c₃.nmem →
          (∀ a, a < bPr ∨ bPr + n ≤ a → c₃.nmem a = c.nmem a) → c₃.output = c.output →
          ∃ c' k, Exec P W (.instr (.addN 230 230 141)) c₃ c' k ∧ I (i + 1) c' ∧ k ≤ 1 := by
        intro c₃ hw₃ e230 er eP ef eo
        have e141 : c₃.nreg 141 = 1 := (er 141 (by omega)).trans f141
        have ea := Exec.addN (P := P) hw₃ 230 230 141 (by rw [e230, e141]; omega)
        refine ⟨_, 1, ea, ⟨ea.wb_right, by config_simp; rw [e230, e141], ?_, by omega,
          by config_simp; exact eP, by config_simp; exact ef, fun r hr' => ?_,
          by config_simp; exact eo⟩, le_rfl⟩
        · config_simp; rw [er 244 (by omega), fr 244 (by omega), h244']
        · config_simp; simp only [upd_apply]
          split_ifs with h'
          · omega
          · rw [er r (by omega), fr r (by omega)]; exact hr r hr'
      unfold pbody
      refine spec_seq ⟨c₂, 14, e₂, ?_⟩
      refine spec_seq ?_
      by_cases hl : Lv lb A h i
      · refine spec_ifLtN_true (by rw [f141]; exact f235.2 hl.1) ?_
        refine spec_ifLtN_true (by rw [f140]; exact f236.2 hl.2) ?_
        obtain ⟨mV, hVn⟩ := hV _ hAi
        have mV' : c₂.nmem (bV + A i) = V (A i) := by
          rw [fm, hf _ (Or.inl (by omega))]; exact mV
        have f162 : c₂.nreg 162 = bV := (fr 162 (by omega)).trans g162
        have f215 : c₂.nreg 215 = bPr := (fr 215 (by omega)).trans g215
        have f240 : c₂.nreg 240 = c0 := (fr 240 (by omega)).trans g240
        unfold pact
        refine spec_seq ?_
        exec_block
        · rw [f162, f233]; omega
        · config_simp; simp only [f162, f233, mV']
          have := hc.1 240; have := hw₂.1 240; omega
        rename_i hwb
        simp only [f162, f233, mV', f240] at hwb ⊢
        by_cases hc0 : V (A i) ≠ c0
        · refine spec_ifLtN_true (by config_simp; rw [f140]; omega) ?_
          exec_block
          · config_simp; rw [f215]; omega
          rename_i hwd
          simp only [f215] at hwd ⊢
          obtain ⟨c', k', e', hI', hk'⟩ := hstep _ hwd (by config_simp; exact f230)
            (fun r hr' => by config_simp; simp only [upd_apply]; split_ifs <;> omega)
            (by config_simp; rw [fm, f233]; exact hP.store ⟨hl, hc0⟩ hVn)
            (fun a ha => by
              config_simp; rw [upd_other _ _ _ (by omega), fm]; exact hf a ha)
            (by config_simp; rw [fo, ho])
          exact ⟨c', k', e', hI', by omega⟩
        · refine spec_ifLtN_false (by config_simp; rw [f140]; omega) ?_
          refine spec_skip ‹_› ?_
          obtain ⟨c', k', e', hI', hk'⟩ := hstep _ ‹_› (by config_simp; exact f230)
            (fun r hr' => by config_simp; simp only [upd_apply]; split_ifs <;> omega)
            (by config_simp; rw [fm]; exact hP.skip fun hq => hc0 hq.2)
            (fun a ha => by config_simp; rw [fm]; exact hf a ha) (by config_simp; rw [fo, ho])
          exact ⟨c', k', e', hI', by omega⟩
      · have hnq : ¬ Q i := fun hq => hl hq.1
        by_cases hl1 : lb (i / 3) = h
        · refine spec_ifLtN_true (by rw [f141]; exact f235.2 hl1) ?_
          have hl2 : ¬ lb (A i / 3) ≠ h := fun h2 => hl ⟨hl1, h2⟩
          refine spec_ifLtN_false (by rw [f140]; exact fun h' => hl2 (f236.1 h')) ?_
          refine spec_skip hw₂ ?_
          obtain ⟨c', k', e', hI', hk'⟩ := hstep _ hw₂ f230 (fun r _ => rfl)
            (by rw [fm]; exact hP.skip hnq) (fun a ha => by rw [fm]; exact hf a ha)
            (by rw [fo, ho])
          exact ⟨c', k', e', hI', by omega⟩
        · refine spec_ifLtN_false (by rw [f141]; exact fun h' => hl1 (f235.1 h')) ?_
          refine spec_skip hw₂ ?_
          obtain ⟨c', k', e', hI', hk'⟩ := hstep _ hw₂ f230 (fun r _ => rfl)
            (by rw [fm]; exact hP.skip hnq) (fun a ha => by rw [fm]; exact hf a ha)
            (by rw [fo, ho])
          exact ⟨c', k', e', hI', by omega⟩)
    (by omega) ⟨e₁.wb_right, by config_simp; exact r140, by config_simp; exact h244, by omega,
      fun v hv => ⟨fun ⟨x, hx, _⟩ => absurd hx (by omega), fun _ => rfl⟩, fun a _ => rfl,
      fun r hr => by
        show upd c.nreg 230 (c.nreg 140) r = c.nreg r
        simp only [upd_apply]; split_ifs <;> omega, rfl⟩
  obtain ⟨-, -, -, -, hP', hf', hr', ho'⟩ := hI
  exact ⟨c₂, 1 + t, .seq e₁ e, by omega, hP', hf', hr', ho'⟩

end proofs

/-! ### The labels and the component -/

section Bridge

open Map CycleSearch

variable {D P : Type*} [Fintype D] [DecidableEq D] [Fintype P] [DecidableEq P] {M : Map D P}
  {T₀ T : M.SpTree} {k n : ℕ} {cd : D ≃ Fin (3 * k)} {A Tm : ℕ → ℕ}
  (hC : Coded M T₀ k cd A Tm) (vi : P ≃ Fin n) {V L : ℕ → ℕ}
  (hV : ∀ x, V (cd x) = vi (M.vert x)) (hL : ∀ v, L (vi v) = T.height v)
include hC hV hL

/-- **The faces with the label of a component are its faces.** For labels `lb` of the components
of the flagged faces (with `lb g = 0` exactly at the faces not flagged), the face of a dart `y`
has the label of a face `F` off `zone (T.low l)` if and only if it lies in the component of
`F`. -/
theorem lab_iff_comp {l : ℕ} {lb : ℕ → ℕ}
    (hlb : ∀ f < k, ∀ g < k, 0 < flagF l V L f → 0 < flagF l V L g →
      (lb f = lb g ↔ Relation.ReflTransGen (FA k A (flagF l V L)) f g))
    (hz : ∀ g < k, lb g = 0 ↔ flagF l V L g = 0) {F : M.Face} (hF : F ∉ M.zone (T.low l))
    (y : D) : lb ((cd y : ℕ) / 3) = lb (fi cd F) ↔ M.face y ∈ M.comp (T.low l) F := by
  have hAv := flagF_pos_iff hC vi hV hL (T := T) l
  rw [← hC.fi_face]
  by_cases hG : M.face y ∈ M.zone (T.low l)
  · have h1 : lb (fi cd (M.face y)) = 0 := (hz _ (hC.fi_lt _)).2 (by
      have := (hAv (M.face y)).not.2 (not_not.2 hG); omega)
    have h2 : lb (fi cd F) ≠ 0 := fun h => by
      have := (hz _ (hC.fi_lt F)).1 h
      have := (hAv F).2 hF
      omega
    rw [h1]
    exact ⟨fun h => absurd h.symm h2, fun h => ((Map.mem_comp.1 h).1 hG).elim⟩
  · rw [eq_comm]; exact label_eq_iff hC hAv hlb hF hG

/-- **The weight of a label is the weight of the strict inside of its component.** -/
theorem sm_eq_ins (hM : M.IsPlane) (hT : IsBFS T) (h3 : ∀ d : D, M.φ (M.φ (M.φ d)) = d)
    {l : ℕ} (hl : 1 ≤ l) (wP : P → ℕ) {fd w : ℕ → ℕ} (fdD : P → D)
    (hfdD : ∀ v, M.vert (fdD v) = v) (hfd : ∀ v, fd (vi v) = cd (fdD v))
    (hw : ∀ v, w (vi v) = wP v) {lb : ℕ → ℕ}
    (hlb : ∀ f < k, ∀ g < k, 0 < flagF l V L f → 0 < flagF l V L g →
      (lb f = lb g ↔ Relation.ReflTransGen (FA k A (flagF l V L)) f g))
    {v : P} (hv : l < T.height v) :
    sm l L fd lb w n (lb (fd (vi v) / 3)) =
      ∑ u ∈ ins (M.comp (T.low l) (M.face (fdD v))), wP u := by
  classical
  have hAv := flagF_pos_iff hC vi hV hL (T := T) l
  have hlab : ∀ u : P, l < T.height u →
      (lb (fd (vi u) / 3) = lb (fd (vi v) / 3) ↔
        M.face (fdD u) ∈ M.comp (T.low l) (M.face (fdD v))) := fun u hu => by
    rw [hfd, hfd, ← hC.fi_face, ← hC.fi_face, eq_comm]
    exact label_eq_iff hC hAv hlb (notMem_zone_of_lt hT h3 hv (hfdD v))
      (notMem_zone_of_lt hT h3 hu (hfdD u))
  have hins : ins (M.comp (T.low l) (M.face (fdD v))) = univ.filter (fun u =>
      l < T.height u ∧ M.face (fdD u) ∈ M.comp (T.low l) (M.face (fdD v))) := by
    ext u; rw [mem_filter, mem_ins_comp_iff hM hT h3 hl (hfdD u)]; simp
  rw [hins, sm, sum_range_vi vi, sum_filter]
  refine sum_congr rfl fun u _ => ?_
  rw [hL, hw]
  by_cases hu : l < T.height u
  · simp only [hu, true_and, hlab u hu]
  · simp only [hu, false_and, ↓reduceIte]

omit [DecidableEq P] hC hV hL in
/-- The numeric comparison with `2/3` of the total. -/
theorem lt_wR {wP : P → ℕ} {S : Finset P} (h : 2 * ∑ u, wP u < 3 * ∑ u ∈ S, wP u) :
    2 / 3 < ∑ u ∈ S, wR wP u := by
  have hS : ∑ u ∈ S, wP u ≤ ∑ u, wP u := sum_le_sum_of_subset (subset_univ _)
  have hpos : (0 : ℝ) < ∑ u, (wP u : ℝ) := by
    have : 0 < ∑ u, wP u := by omega
    exact_mod_cast this
  unfold wR
  rw [← sum_div, lt_div_iff₀ hpos]
  have : (2 * ∑ u, wP u : ℝ) < 3 * ∑ u ∈ S, wP u := by exact_mod_cast h
  push_cast at this
  linarith

end Bridge

/-! ### The program -/

section Whole

open Map CycleSearch

variable {D P : Type*} [Fintype D] [DecidableEq D] [Fintype P] [DecidableEq P] {M : Map D P}
  {T₀ T : M.SpTree} {k n : ℕ} {cd : D ≃ Fin (3 * k)} {A Tm V L fd w : ℕ → ℕ}
  {vi : P ≃ Fin n} {wP : P → ℕ} {fdD : P → D}
  {W : ℕ} {P' : Input} {bA bL bS bR bV bLv bF bw bSum bPr : ℕ}

set_option maxHeartbeats 1000000 in
/-- **The inner region on the machine.** For a coded triangulation with a breadth-first tree `T`
(levels, darts at the vertices and weights in memory, `MillerProg.Setup`), whose parent darts are
at `bPr`, and a heavy level `l ≥ 1` in `r160`, the program `iprog` ends within
`247 k + 39 n + 33` steps with the parent darts of the tree `T₁` of an inner region
(`PlanarSeparator.Map.Inner`) at `bPr` and the number of its vertex `c₀` in `r240`. -/
theorem iprog_inner (hS : Setup M T₀ T k n cd A Tm V L fd w vi wP fdD)
    (htri : ∀ δ : D, M.IsTriangle δ)
    (hlay : bR + 3 * k ≤ bPr ∧ bV + 3 * k ≤ bPr ∧ bPr + n ≤ bA ∧ bLv + n ≤ bA ∧
      bF + n ≤ bA ∧ bw + n ≤ bA ∧ bA + k ≤ bL ∧ bL + k ≤ bS ∧ bS + k ≤ bSum)
    (hW : bSum + 3 * k + 4 * n + 1 ≤ W ∧ 3 * ∑ v, wP v ≤ W) (hk : 0 < k) {l : ℕ}
    (hl1 : 1 ≤ l) (hl : l < n) (hheavy : Heavy T (wR wP) l)
    (c : Config) (hc : WordsBounded W c) (hR : CR k bA bL bS bR c)
    (hH : HR l n bV bLv bF bw bSum c) (h168 : c.nreg 168 = ∑ v, wP v)
    (h215 : c.nreg 215 = bPr) (hm : InMem k n bR bV bLv bF bw A V L fd w c.nmem)
    (hpar : ∀ v (h : v ≠ T.root), (cd (T.par v h) : ℕ) = c.nmem (bPr + vi v)) :
    ∃ c' t, Exec P' W iprog c c' t ∧ t ≤ 247 * k + 39 * n + 33 ∧
      (∃ (H : Finset M.Face) (K₀ : Finset P) (c₀ : P) (T₁ : M.SpTree),
        Inner T (wR wP) l H K₀ c₀ T₁ ∧ K₀ ⊆ T.lvl l ∧ T₁.root = T.root ∧
        c'.nreg 240 = vi c₀ ∧
        ∀ v (h : v ≠ T₁.root), (cd (T₁.par v h) : ℕ) = c'.nmem (bPr + vi v)) ∧
      (∀ r, r < 150 ∨ (160 ≤ r ∧ r < 169) ∨ (180 ≤ r ∧ r < 183) ∨ (186 ≤ r ∧ r < 230) ∨
        245 ≤ r → c'.nreg r = c.nreg r) ∧
      (∀ a, a < bPr ∨ (bPr + n ≤ a ∧ a < bA) ∨ bSum + k + 1 ≤ a → c'.nmem a = c.nmem a) ∧
      c'.output = c.output := by
  obtain ⟨l0, l0', l00, l3, l4, l5, l6, l7, l8⟩ := hlay
  have l1 : bR + 3 * k ≤ bA := by omega
  have l2 : bV + 3 * k ≤ bA := by omega
  obtain ⟨m1, m2, m3, m4, m5⟩ := hm
  have hC := hS.coded
  have h3 := hS.tri
  have hA := revOk hC
  unfold iprog
  -- the sums are cleared
  obtain ⟨c₁, t₁, e₁, ht₁, hz₁, hr₁, hf₁, ho₁⟩ :=
    zpass_exec (P' := P') (by omega : bSum + k + 1 ≤ W) c hc hR hH
  have hR₁ : CR k bA bL bS bR c₁ := hR.of fun r hr => hr₁ r (Or.inl (by omega))
  have hH₁ : HR l n bV bLv bF bw bSum c₁ := hH.of fun r h1 h2 => hr₁ r (Or.inl (by omega))
  have k₁ : ∀ a < bSum, c₁.nmem a = c.nmem a := fun a ha => hf₁ a (Or.inl ha)
  -- the heavy test: labels and sums
  have htot : ∑ u ∈ range n, w u = ∑ v, wP v := by
    rw [sum_range_vi vi]; exact sum_congr rfl fun u _ => hS.hw u
  have hVn : ∀ x < 3 * k, V x < n := fun x hx => by
    have : V x = vi (M.vert (cd.symm ⟨x, hx⟩)) := by rw [← hS.hV]; simp
    rw [this]; exact (vi _).2
  have hFk : ∀ v < n, fd v < 3 * k := fun v hv => by
    have : fd v = cd (fdD (vi.symm ⟨v, hv⟩)) := by rw [← hS.hfd]; simp
    rw [this]; exact (cd _).2
  obtain ⟨c₂, t₂, e₂, ht₂, lb, hz, hcls, -, -, hS₂, hlb₂, hr₂, hf₂, ho₂⟩ :=
    hvy_exec (P := P') (L := L) hA ⟨l1, l2, l3, l4, l5, l6, l7, l8⟩
      ⟨by omega, hW.2⟩ htot c₁ e₁.wb_right hR₁ hH₁
      (by rw [hr₁ 168 (Or.inl (by omega))]; exact h168)
      (fun x hx => by rw [k₁ _ (by omega)]; exact m1 x hx)
      (fun x hx => ⟨by rw [k₁ _ (by omega)]; exact m2 x hx, hVn x hx⟩)
      (fun v hv => by rw [k₁ _ (by omega)]; exact m3 v hv)
      (fun v hv => ⟨by rw [k₁ _ (by omega)]; exact m4 v hv, hFk v hv⟩)
      (fun v hv => by rw [k₁ _ (by omega)]; exact m5 v hv) hz₁
  have hR₂ : CR k bA bL bS bR c₂ := hR₁.of fun r hr => hr₂ r (Or.inl hr)
  have hH₂ : HR l n bV bLv bF bw bSum c₂ :=
    hH₁.of fun r h1 h2 => hr₂ r (Or.inr (Or.inl ⟨h1, by omega⟩))
  have k₂ : ∀ a < bA, c₂.nmem a = c.nmem a := fun a ha => by
    rw [hf₂ a (Or.inl ha), k₁ a (by omega)]
  -- a heavy label
  obtain ⟨c₃, t₃, e₃, ht₃, hP₃, hr₃, hm₃, ho₃⟩ := hpass_exec (P := P') (fd := fd) (lb := lb)
    (L := L) (S := sm l L fd lb w n) (tot := ∑ v, wP v) ⟨l3, l4, l6, by omega⟩
    ⟨by omega, hW.2⟩ c₂ e₂.wb_right hR₂ hH₂
    (by rw [hr₂ 168 (Or.inr (Or.inl ⟨by omega, by omega⟩)), hr₁ 168 (Or.inl (by omega))];
        exact h168)
    (fun v hv => by rw [k₂ _ (by omega)]; exact m3 v hv)
    (fun v hv => ⟨by rw [k₂ _ (by omega)]; exact m4 v hv, hFk v hv⟩) hlb₂
    (fun x hx => ⟨hS₂ x hx, by rw [← htot]; exact sm_le _ _ _ _ _ _ _⟩)
  have hex : ∃ v < n, l < L v ∧ 2 * ∑ v, wP v < 3 * sm l L fd lb w n (lb (fd v / 3)) := by
    obtain ⟨v, hv, hlv, h⟩ := (test_iff_heavy hC vi hS.hV hS.hL hS.plane hS.bfs h3 hl1 wP fdD
      hS.hfdD hS.hfd hS.hw hcls).2 hheavy
    exact ⟨v, hv, hlv, by rw [← htot]; exact h⟩
  obtain ⟨hvH, hlvH, hSH, h237⟩ := hP₃ hex
  set vH := c₃.nreg 238
  set vHP := vi.symm ⟨vH, hvH⟩
  have hviH : (vi vHP : ℕ) = vH := by simp [vHP]
  have hhtH : l < T.height vHP := by rw [← hS.hL, hviH]; exact hlvH
  set F := M.face (fdD vHP)
  have hFz : F ∉ M.zone (T.low l) := notMem_zone_of_lt hS.bfs h3 hhtH (hS.hfdD vHP)
  have hfiF : fi cd F = fd vH / 3 := by rw [hC.fi_face, ← hS.hfd, hviH]
  have hlab : ∀ y : D, lb ((cd y : ℕ) / 3) = c₃.nreg 237 ↔
      M.face y ∈ M.comp (T.low l) F := fun y => by
    rw [h237, ← hfiF]
    exact lab_iff_comp hC vi hS.hV hS.hL hcls (fun g hg => hz g hg) hFz y
  have hheavyH : 2 / 3 < ∑ v ∈ ins (M.comp (T.low l) F), wR wP v := by
    apply lt_wR
    rw [← sm_eq_ins hC vi hS.hV hS.hL hS.plane hS.bfs h3 hl1 wP fdD hS.hfdD hS.hfd hS.hw hcls
      hhtH, hviH]
    exact hSH
  -- a dart leaving the component
  have hR₃ : CR k bA bL bS bR c₃ := hR₂.of fun r hr => hr₃ r (Or.inl (by omega))
  have mA₃ : ∀ x < 3 * k, c₃.nmem (bR + x) = A x ∧ A x < 3 * k := fun x hx =>
    ⟨by rw [hm₃, k₂ _ (by omega)]; exact m1 x hx, (hA x hx).1⟩
  have mlb₃ : ∀ g < k, c₃.nmem (bL + g) = lb g := fun g hg => by rw [hm₃]; exact (hlb₂ g hg).1
  have mV₃ : ∀ x < 3 * k, c₃.nmem (bV + x) = V x := fun x hx => by
    rw [hm₃, k₂ _ (by omega)]; exact m2 x hx
  have g162 : c₃.nreg 162 = bV := by
    rw [hr₃ 162 (by omega), hr₂ 162 (Or.inr (Or.inl ⟨by omega, by omega⟩)),
      hr₁ 162 (Or.inl (by omega))]; exact hH.r162
  have hLv : ∀ y : D, Lv lb A (c₃.nreg 237) (cd y) ↔
      M.face y ∈ M.comp (T.low l) F ∧ M.face (M.α y) ∉ M.comp (T.low l) F := fun y => by
    unfold Lv
    rw [hlab y, hC.A_cd, ne_eq, hlab (M.α y)]
  obtain ⟨c₄, t₄, e₄, ht₄, hP₄, h239, h240, h244, hr₄, hm₄, ho₄⟩ := xpass_exec (P := P')
    (lb := lb) (A := A) (V := V) hk ⟨by omega, by omega, by omega⟩ c₃ e₃.wb_right hR₃ g162 rfl
    mA₃ mlb₃ mV₃
  have hexL : ∃ x < 3 * k, Lv lb A (c₃.nreg 237) x := by
    obtain ⟨d₀, hd₀⟩ := hS.plane.exists_dart T.root
    obtain ⟨d, hd1, hd2⟩ := exists_bd_comp hS.plane (B := T.low l) (d₀ := d₀)
      (by rw [hd₀]; exact root_mem_low hS.bfs hl1) hFz
    exact ⟨cd d, (cd d).2, (hLv d).2 ⟨hd1, hd2⟩⟩
  set x₀ := c₄.nreg 239
  set x₀D := cd.symm ⟨x₀, h239⟩
  have hcx₀ : (cd x₀D : ℕ) = x₀ := by simp [x₀D]
  have hx₀ := (hLv x₀D).1 (by rw [hcx₀]; exact hP₄ hexL)
  obtain ⟨K₀, T₁, hI, hK, hroot, -, hpin, hpoff⟩ :=
    inner_explicit hS.plane htri hS.bfs hl1 hFz hheavyH hx₀.1 hx₀.2
  have hc₀ : V x₀ = vi (M.vert x₀D) := by rw [← hS.hV, hcx₀]
  -- the redirected parent darts
  have hR₄ : CR k bA bL bS bR c₄ := hR₃.of fun r hr => hr₄ r (Or.inl (by omega))
  have g215 : c₄.nreg 215 = bPr := by
    rw [hr₄ 215 (by omega), hr₃ 215 (by omega), hr₂ 215 (Or.inr (Or.inr (by omega))),
      hr₁ 215 (Or.inr (by omega))]; exact h215
  obtain ⟨c₅, t₅, e₅, ht₅, hP₅, hf₅, hr₅, ho₅⟩ := ppass_exec (P := P') (lb := lb) (A := A)
    (V := V) (h := c₃.nreg 237) (c0 := V x₀) (n := n) ⟨l0, l0', by omega⟩ (by omega) c₄
    e₄.wb_right hR₄ (by rw [hr₄ 162 (by omega)]; exact g162) g215
    (hr₄ 237 (Or.inr (Or.inl ⟨by omega, by omega⟩))) (by rw [h240]) h244
    (fun x hx => by rw [hm₄]; exact mA₃ x hx) (fun g hg => by rw [hm₄]; exact mlb₃ g hg)
    (fun x hx => ⟨by rw [hm₄]; exact mV₃ x hx, hVn x hx⟩)
  refine ⟨c₅, t₁ + (t₂ + (t₃ + (t₄ + t₅))), .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ e₅))),
    by omega, ⟨_, K₀, M.vert x₀D, T₁, hI, hK, hroot, ?_, fun v h => ?_⟩, fun r hr => ?_,
    fun a ha => ?_, by rw [ho₅, ho₄, ho₃, ho₂, ho₁]⟩
  · rw [hr₅ 240 (Or.inr (Or.inl ⟨by omega, by omega⟩)), h240, hc₀]
  · by_cases hexv : ∃ x < 3 * k, (Lv lb A (c₃.nreg 237) x ∧ V (A x) ≠ V x₀) ∧ V (A x) = vi v
    · obtain ⟨x, hx, ⟨hQ, hne⟩, he, hmx⟩ := (hP₅ _ (vi v).2).1 hexv
      have he' : V (A x) = vi v := he
      set y := cd.symm ⟨x, hx⟩
      have hcy : (cd y : ℕ) = x := by simp [y]
      have hy := (hLv y).1 (by rw [hcy]; exact hQ)
      have hAy : (cd (M.α y) : ℕ) = A x := by rw [← hC.A_cd, hcy]
      have hvy : M.vert (M.α y) = v := by
        apply vi.injective; apply Fin.ext; rw [← hS.hV, hAy, he']
      have hne' : M.vert (M.α y) ≠ M.vert x₀D := fun e => by
        apply hne; rw [← hAy, hS.hV, e, hc₀]
      subst hvy
      rw [hpin y hy.1 hy.2 hne' h, hAy, hmx]
    · have h' : v ≠ T.root := by rw [← hroot]; exact h
      rw [(hP₅ _ (vi v).2).2 hexv, hm₄, hm₃, k₂ _ (by have := (vi v).2; omega), ← hpar v h']
      congr 2
      refine hpoff v h h' ?_
      by_cases hvc : v = M.vert x₀D
      · exact Or.inr hvc
      · left
        intro y hy1 hy2 hvy
        apply hexv
        have hAy : (cd (M.α y) : ℕ) = A (cd y) := by rw [hC.A_cd]
        refine ⟨cd y, (cd y).2, ⟨(hLv y).2 ⟨hy1, hy2⟩, ?_⟩, ?_⟩
        · rw [← hAy, hS.hV, hvy, hc₀]
          exact fun e => hvc (vi.injective (Fin.ext e))
        · rw [← hAy, hS.hV, hvy]
  · rw [hr₅ r (by omega), hr₄ r (by omega), hr₃ r (by omega), hr₂ r (by omega),
      hr₁ r (by omega)]
  · rw [hf₅ a (by omega), hm₄, hm₃, hf₂ a (by omega), hf₁ a (by omega)]

end Whole

end MillerProg

end PlanarSeparator
