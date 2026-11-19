module

public import PlanarSeparator.Machine.MillerS910

/-!
# Miller's separator on the machine: the deep case of step 9, the component `Y`

In the deep case of `PlanarSeparator.Map.bandSep` (both faces of the balanced dart `δ` avoid the
levels `< l₂`), the separator `PlanarSeparator.Map.deepSep` reads the component
`Y = M.comp (T.low l₂) (M.face δ)` and the weight of its strict inside. After `millerB` the labels
of step 7 are not available, so `s10hvy` reruns the heavy test `hvy` of step 3 at the level `l₂`
(in a fresh region: scratch at `bA'`, `bL'`, `bS'`, clear sums at `bSum'`):

* `s10reg`: the registers `CR`/`HR` of `hvy` and `r250 = bw` from the inputs above `590`;
* `wsum`: the total weight (into `r168`);
* `hvy` at `l₂ = r160`: the labels of the faces at `bL'` and the label sums at `bSum'`;
* `s10lab`: the label `h = lb (δ / 3)` of `Y` (`r597`) and the sum of its strict inside (`r599`).

**`s10hvy_spec`**: within `101 k + 27 n + 36` steps, the label of a face is `h` iff the face lies
in `Y`, `r599 = ∑ v ∈ ins Y, wP v` and `r168 = ∑ v, wP v` (so the heavy test `1/3 ≤ ∑ ins Y` of
`deepSep` is `r168 ≤ 3 r599`, `MillerProg.third_le_iff`).
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace PlanarSeparator

namespace MillerProg

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs Finset Map CycleSearch

/-- The registers of `hvy` (`CR`, `HR`) and of `wsum`, from the inputs. -/
def s10reg : List Instr :=
  [.constN 140 0, .constN 141 1, .constN 142 3, .copyN 143 530, .copyN 144 591, .copyN 145 592,
    .copyN 146 593, .constN 147 0, .copyN 161 505, .copyN 162 502, .copyN 163 567,
    .copyN 164 595, .copyN 165 596, .copyN 166 594, .copyN 250 596]

/-- The label `r597` of the face of `δ = r500` and the sum `r599` of its label. -/
def s10lab : List Instr :=
  [.divN 598 500 535, .addN 598 592 598, .loadN 597 598, .addN 598 594 597, .loadN 599 598]

/-- **The component `Y` of `δ` at level `l₂`**: labels and the weight of its strict inside. -/
def s10hvy : Stmt :=
  .seq (block s10reg) <| .seq wsum <| .seq (.instr (.copyN 168 320)) <| .seq hvy (block s10lab)

section Deep

variable {D Q : Type*} [Fintype D] [DecidableEq D] [Fintype Q] [DecidableEq Q] {M : Map D Q}

set_option maxHeartbeats 8000000 in
/-- **The component of `δ` at level `l₂` on the machine.** -/
theorem s10hvy_spec {T T₁ : M.SpTree} {k n : ℕ} {cd : D ≃ Fin (3 * k)} {vi : Q ≃ Fin n}
    {A V : ℕ → ℕ} (wP : Q → ℕ) {fdD : Q → D} {W : ℕ} {P : Input} {c : Config}
    {bV bPr bLv bF bw bA' bL' bS' bSum' l₂ : ℕ} {δ : D}
    (hM : M.IsPlane) (hT : IsBFS T) (hT3 : ∀ δ, M.IsTriangle δ) (hl2 : 1 ≤ l₂) (hl2n : l₂ ≤ n)
    (hAcd : ∀ x, A (cd x) = cd (M.α x)) (hφ : ∀ x, (cd (M.φ x) : ℕ) = phi3 (cd x))
    (hV : ∀ x, V (cd x) = vi (M.vert x)) (hfdD : ∀ u, M.vert (fdD u) = u)
    (hz1 : M.face δ ∉ M.zone (T.low l₂))
    (hlay : 3 * k ≤ bA' ∧ bV + 3 * k ≤ bA' ∧ bLv + n ≤ bA' ∧ bF + n ≤ bA' ∧ bw + n ≤ bA' ∧
      bA' + k ≤ bL' ∧ bL' + k ≤ bS' ∧ bS' + k ≤ bSum' ∧ bSum' + 3 * k + 4 * n + 1 ≤ W)
    (hWt : 3 * ∑ v, wP v ≤ W) (hc : WordsBounded W c)
    (h160 : c.nreg 160 = l₂) (h500 : c.nreg 500 = cd δ) (h535 : c.nreg 535 = 3)
    (h502 : c.nreg 502 = bV) (h505 : c.nreg 505 = n) (h530 : c.nreg 530 = k)
    (h567 : c.nreg 567 = bLv) (h591 : c.nreg 591 = bA') (h592 : c.nreg 592 = bL')
    (h593 : c.nreg 593 = bS') (h594 : c.nreg 594 = bSum') (h595 : c.nreg 595 = bF)
    (h596 : c.nreg 596 = bw)
    (mA : ∀ x < 3 * k, c.nmem x = A x) (mV : ∀ x < 3 * k, c.nmem (bV + x) = V x)
    (mL : ∀ v, c.nmem (bLv + vi v) = T.height v)
    (hPr : ∀ v (h : v ≠ T₁.root), c.nmem (bPr + vi v) = cd (T₁.par v h))
    (mF : ∀ u, c.nmem (bF + vi u) = cd (fdD u)) (mW : ∀ v, c.nmem (bw + vi v) = wP v)
    (hz : ∀ x ≤ k, c.nmem (bSum' + x) = 0) :
    ∃ c' t, Exec P W s10hvy c c' t ∧ t ≤ 101 * k + 27 * n + 36 ∧
      (∀ y : D, c'.nmem (bL' + (cd y : ℕ) / 3) = c'.nreg 597 ↔
        M.face y ∈ M.comp (T.low l₂) (M.face δ)) ∧
      c'.nreg 599 = ∑ v ∈ ins (M.comp (T.low l₂) (M.face δ)), wP v ∧
      c'.nreg 168 = ∑ v, wP v ∧
      (∀ a, (a < bA' ∨ bSum' + k + 1 ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, 400 ≤ r → r ≠ 597 → r ≠ 598 → r ≠ 599 → c'.nreg r = c.nreg r) ∧
      c'.output = c.output := by
  classical
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9⟩ := hlay
  have hk : 0 < k := by
    obtain ⟨d⟩ : Nonempty D := ⟨δ⟩
    have := (cd d).2; omega
  have h3 : ∀ d : D, M.φ (M.φ (M.φ d)) = d := fun d => (hT3 d).φ_three
  set w : ℕ → ℕ := fun u => c.nmem (bw + u) with hwd
  set L : ℕ → ℕ := fun u => c.nmem (bLv + u) with hLd
  set fd : ℕ → ℕ := fun u => c.nmem (bF + u) with hfd
  set Pr : ℕ → ℕ := fun u => c.nmem (bPr + u) with hPrd
  have hPr' : ∀ v (h : v ≠ T₁.root), Pr (vi v) = cd (T₁.par v h) := hPr
  have hin := rootIn_tree cd vi T₁ hAcd hV hPr'
  have hsumw : ∑ u ∈ range n, w u = ∑ v, wP v := by rw [sum_range_vi vi]; exact sum_congr rfl fun v _ => mW v
  -- 0. the registers
  obtain ⟨c₁, t₁, e₁, ht₁, hCR, hHR, q250, hr₁, hm₁, ho₁⟩ : ∃ c₁ t₁,
      Exec P W (block s10reg) c c₁ t₁ ∧ t₁ = 15 ∧ CR k bA' bL' bS' 0 c₁ ∧
      HR l₂ n bV bLv bF bw bSum' c₁ ∧ c₁.nreg 250 = bw ∧
      (∀ r, (r < 140 ∨ (147 < r ∧ r < 161) ∨ (166 < r ∧ r ≠ 250)) → c₁.nreg r = c.nreg r) ∧
      c₁.nmem = c.nmem ∧ c₁.output = c.output := by
    unfold s10reg
    exec_block
    all_goals try omega
    refine ⟨rfl, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_,
      fun r hr => ?_, rfl, rfl⟩
    all_goals try (config_simp <;> first | assumption | omega)
    simp (disch := omega) only [Config.nreg_mk, upd_other]
  have hw₁ := e₁.wb_right
  -- 1. the total weight
  obtain ⟨c₂, t₂, e₂, ht₂, h320, hr₂, hm₂, ho₂⟩ := wsum_exec (P := P) (n := n) (bW := bw) (w := w)
    (by omega) (by rw [hsumw]; omega) c₁ hw₁ hCR.r140 hCR.r141 hHR.r161 q250
    (fun u _ => by rw [hm₁])
  have hw₂ := e₂.wb_right
  have e₃ := Exec.copyN (P := P) hw₂ 168 320
  set c₃ : Config := { c₂ with nreg := upd c₂.nreg 168 (c₂.nreg 320) }
  have k₃ : ∀ r, r ≠ 168 → c₃.nreg r = c₂.nreg r := fun r hr => upd_other _ _ _ hr
  have q168 : c₃.nreg 168 = ∑ u ∈ range n, w u := by
    show upd c₂.nreg 168 (c₂.nreg 320) 168 = _; rw [upd_same, h320]
  have hw₃ := e₃.wb_right
  have fm₃ : c₃.nmem = c.nmem := by rw [show c₃.nmem = c₂.nmem from rfl, hm₂, hm₁]
  have K₃ : ∀ r, r ≠ 168 → r ≠ 320 → r ≠ 365 → r ≠ 366 → r ≠ 367 → c₃.nreg r = c₁.nreg r :=
    fun r a b d e f => by rw [k₃ r a, hr₂ r b d e f]
  -- 2. the heavy test at `l₂`
  have hFl : ∀ v < n, c₃.nmem (bF + v) = fd v ∧ fd v < 3 * k := fun v hv => by
    obtain ⟨u, rfl⟩ := exists_vi vi hv
    refine ⟨by rw [fm₃], ?_⟩
    show c.nmem (bF + vi u) < 3 * k
    rw [mF]; exact (cd _).2
  obtain ⟨c₄, t₄, e₄, ht₄, lb, hlb0, hcc, -, -, hsm, hbl, hr₄, hm₄, ho₄⟩ :=
    hvy_exec (P := P) (k := k) (A := A) (V := V) (L := L) (fd := fd) (w := w)
      (tot := ∑ u ∈ range n, w u) (revOk_of cd hAcd)
      ⟨by omega, l2, l3, l4, l5, l6, l7, l8⟩ ⟨by omega, by rw [hsumw]; exact hWt⟩ rfl c₃ hw₃
      (hCR.of fun r hr => K₃ r (by omega) (by omega) (by omega) (by omega) (by omega))
      (hHR.of fun r h1 h2 => K₃ r (by omega) (by omega) (by omega) (by omega) (by omega)) q168
      (fun x hx => by rw [zero_add, fm₃]; exact mA x hx)
      (fun x hx => ⟨by rw [fm₃]; exact mV x hx, hin.V_lt x hx⟩)
      (fun v _ => by rw [fm₃]) hFl (fun v _ => by rw [fm₃])
      (fun x hx => by rw [fm₃]; exact hz x hx)
  have hw₄ := e₄.wb_right
  -- 3. the label of `Y` and its sum
  have g500 : c₄.nreg 500 = cd δ := by
    rw [hr₄ 500 (Or.inr (Or.inr (by omega))), K₃ 500 (by omega) (by omega) (by omega) (by omega)
      (by omega), hr₁ 500 (Or.inr (Or.inr ⟨by omega, by omega⟩))]; exact h500
  have G : ∀ r, 400 ≤ r → c₄.nreg r = c.nreg r := fun r hr => by
    rw [hr₄ r (Or.inr (Or.inr (by omega))), K₃ r (by omega) (by omega) (by omega) (by omega)
      (by omega), hr₁ r (Or.inr (Or.inr ⟨by omega, by omega⟩))]
  set hδ' := (cd δ : ℕ) / 3
  have hhk : hδ' < k := by have := (cd δ).2; omega
  obtain ⟨c₅, t₅, e₅, ht₅, q597, q599, hr₅, hm₅, ho₅⟩ : ∃ c₅ t₅,
      Exec P W (block s10lab) c₄ c₅ t₅ ∧ t₅ = 5 ∧ c₅.nreg 597 = lb hδ' ∧
      c₅.nreg 599 = sm l₂ L fd lb w n (lb hδ') ∧
      (∀ r, r ≠ 597 → r ≠ 598 → r ≠ 599 → c₅.nreg r = c₄.nreg r) ∧ c₅.nmem = c₄.nmem ∧
      c₅.output = c₄.output := by
    have a535 := G 535 (by omega)
    have a592 := G 592 (by omega)
    have a594 := G 594 (by omega)
    have hb1 := (hbl hδ' hhk)
    have hb2 := hc.1 592
    exec_block
    · config_simp; rw [a592, h592, g500, a535, h535]; omega
    · config_simp; rw [a594, h594, a592, h592, g500, a535, h535, hb1.1]; omega
    refine ⟨rfl, ?_, ?_, fun r a1 a2 a3 => ?_, rfl, rfl⟩
    · config_simp; rw [a592, h592, g500, a535, h535]; exact hb1.1
    · config_simp; rw [a594, h594, a592, h592, g500, a535, h535, hb1.1]; exact hsm _ hb1.2
    · config_simp; simp only [upd_apply]; split_ifs <;> omega
  -- the bridge
  have hC := coded_of_tmark (k := k) (cd := cd) (vi := vi) (A := A) (Pr := Pr) hAcd hφ hPr'
  have hL : ∀ v, L (vi v) = T.height v := mL
  have hAv := flagF_pos_iff hC vi hV hL l₂
  set Y := M.comp (T.low l₂) (M.face δ)
  have hlab : ∀ y : D, lb ((cd y : ℕ) / 3) = lb hδ' ↔ M.face y ∈ Y := by
    intro y
    rw [← hC.fi_face, show hδ' = fi cd (M.face δ) from (hC.fi_face δ).symm]
    by_cases hy : M.face y ∈ M.zone (T.low l₂)
    · have h0 : lb (fi cd (M.face y)) = 0 := (hlb0 _ (hC.fi_lt _)).2 (by
        have := (hAv (M.face y)).not.2 (not_not.2 hy); omega)
      have h1 : lb (fi cd (M.face δ)) ≠ 0 := fun e =>
        absurd ((hlb0 _ (hC.fi_lt _)).1 e) (by have := (hAv (M.face δ)).2 hz1; omega)
      rw [h0]
      exact ⟨fun e => absurd e.symm h1, fun h => absurd hy (Map.mem_comp.1 h).1⟩
    · rw [eq_comm]
      exact label_eq_iff hC hAv hcc hz1 hy
  have hsum : sm l₂ L fd lb w n (lb hδ') = ∑ v ∈ ins Y, wP v := by
    unfold sm
    rw [sum_range_vi vi, ← sum_filter]
    refine sum_congr ?_ fun v _ => mW v
    ext v
    simp only [mem_filter, mem_univ, true_and]
    rw [mem_ins_comp_iff hM hT h3 hl2 (hfdD v), ← hlab]
    show l₂ < c.nmem (bLv + vi v) ∧ lb (c.nmem (bF + vi v) / 3) = _ ↔ _
    rw [mL, mF]
  have e₀ : Exec P W s10hvy c c₅ (t₁ + (t₂ + (1 + (t₄ + t₅)))) :=
    .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ e₅)))
  refine ⟨c₅, _, e₀, by omega, fun y => ?_, by rw [q599, hsum], ?_, fun a ha => ?_,
    fun r a1 a2 a3 a4 => by rw [hr₅ r a2 a3 a4, G r a1], ?_⟩
  · rw [hm₅, q597, (hbl _ (by have := (cd y).2; omega)).1]; exact hlab y
  · rw [hr₅ 168 (by omega) (by omega) (by omega), hr₄ 168 (Or.inr (Or.inl (by omega))), q168,
      hsumw]
  · rw [hm₅, hm₄ a ha, fm₃]
  · rw [ho₅, ho₄, show c₃.output = c₂.output from rfl, ho₂, ho₁]

end Deep

/-! ### A dart leaving `Y` -/

/-- One dart `r450 = x` of the search of a dart leaving `Y` (the test of `bdPass`): if it
leaves, `r445 := x`. -/
def xfBody : Stmt :=
  .seq (block bdTest)
    (.seq (.ifLtN 457 431 (.ifLtN 430 458 (.instr (.copyN 445 450)) .skip) .skip)
      (.instr (.addN 450 450 431)))

/-- **A dart leaving the component of label `h`**, into `r445` (the start `x₀` of `cyWalk`). -/
def xfind : Stmt := .seq (.instr (.copyN 450 430)) (.whileLtN 450 436 xfBody)

section XF

variable {W : ℕ} {P : Input}

set_option maxHeartbeats 4000000 in
/-- **The search of a dart leaving `Y`**: if one exists, `r445` is one. -/
theorem xfind_exec {A lb : ℕ → ℕ} {k h bA bL : ℕ} (hW : bL + k ≤ W ∧ bA + 3 * k ≤ W)
    (c : Config) (hc : WordsBounded W c) (h430 : c.nreg 430 = 0) (h431 : c.nreg 431 = 1)
    (h432 : c.nreg 432 = 3) (h433 : c.nreg 433 = bA) (h435 : c.nreg 435 = bL)
    (h436 : c.nreg 436 = 3 * k) (h437 : c.nreg 437 = h)
    (hA : ∀ x < 3 * k, c.nmem (bA + x) = A x ∧ A x < 3 * k)
    (hlb : ∀ g < k, c.nmem (bL + g) = lb g) :
    ∃ c' t, Exec P W xfind c c' t ∧ t ≤ 20 * (3 * k) + 3 ∧
      ((∃ x < 3 * k, Lv lb A h x) → c'.nreg 445 < 3 * k ∧ Lv lb A h (c'.nreg 445)) ∧
      (∀ r, r ≠ 445 → (r < 450 ∨ 459 ≤ r) → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem ∧
      c'.output = c.output := by
  let I : ℕ → Config → Prop := fun i c' => WordsBounded W c' ∧ c'.nreg 450 = i ∧
    c'.nreg 436 = 3 * k ∧ i ≤ 3 * k ∧
    ((∃ x < i, Lv lb A h x) → c'.nreg 445 < 3 * k ∧ Lv lb A h (c'.nreg 445)) ∧
    (∀ r, r ≠ 445 → (r < 450 ∨ 459 ≤ r) → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem ∧
    c'.output = c.output
  have e₀ := Exec.copyN (P := P) hc 450 430
  set c₀ : Config := { c with nreg := upd c.nreg 450 (c.nreg 430) }
  have hI₀ : I 0 c₀ := ⟨e₀.wb_right, by show upd c.nreg 450 (c.nreg 430) 450 = 0; rw [upd_same, h430],
    by show upd c.nreg 450 (c.nreg 430) 436 = 3 * k
       rw [upd_other _ _ _ (show (436 : ℕ) ≠ 450 by omega), h436], by omega,
    fun ⟨x, hx, _⟩ => absurd hx (by omega),
    fun r a b => upd_other _ _ _ (show r ≠ 450 by omega), rfl, rfl⟩
  obtain ⟨c', t, e, hI', ht⟩ := Exec.forN (P := P) (W := W) (ri := 450) (rN := 436) (N := 3 * k)
    (lo := 0) (B := 18) (body := xfBody) I (fun i c' h => ⟨h.1, h.2.1, h.2.2.1⟩)
    (fun i c₁ ⟨hw, h450, g436, hi, hinv, hr, hm, ho⟩ hlt => by
      have F : ∀ r, r ≠ 445 → (r < 450 ∨ 459 ≤ r) → c₁.nreg r = c.nreg r := hr
      have hAi := hA i hlt
      obtain ⟨c₂, t₂, e₂, rfl, -, i457, i458, hr₂, hm₂, ho₂⟩ := bdTest_exec (P := P) (A := A)
        (lb := lb) (x := i) hW c₁ hw ((F 432 (by omega) (by omega)).trans h432)
        ((F 435 (by omega) (by omega)).trans h435) ((F 433 (by omega) (by omega)).trans h433)
        ((F 437 (by omega) (by omega)).trans h437) h450 hlt (by rw [hm]; exact hAi.1) hAi.2
        (by rw [hm]; exact hlb _ (by omega)) (by rw [hm]; exact hlb _ (by omega))
      have hw₂ := e₂.wb_right
      have g431 : c₂.nreg 431 = 1 := by rw [hr₂ 431 (Or.inl (by omega)), F 431 (by omega) (by omega), h431]
      have g430 : c₂.nreg 430 = 0 := by rw [hr₂ 430 (Or.inl (by omega)), F 430 (by omega) (by omega), h430]
      have g450 : c₂.nreg 450 = i := by rw [hr₂ 450 (Or.inl (by omega)), h450]
      -- the branch
      obtain ⟨c₃, t₃, e₃, ht₃, y1, y2, hr₃, hm₃, ho₃⟩ : ∃ c₃ t₃, Exec P W
          (.ifLtN 457 431 (.ifLtN 430 458 (.instr (.copyN 445 450)) .skip) .skip) c₂ c₃ t₃ ∧
          t₃ ≤ 3 ∧ (Lv lb A h i → c₃.nreg 445 = i) ∧ (¬ Lv lb A h i → c₃.nreg 445 = c₂.nreg 445) ∧
          (∀ r, r ≠ 445 → c₃.nreg r = c₂.nreg r) ∧ c₃.nmem = c₂.nmem ∧ c₃.output = c₂.output := by
        by_cases a1 : c₂.nreg 457 < c₂.nreg 431
        · by_cases a2 : c₂.nreg 430 < c₂.nreg 458
          · have hlv : Lv lb A h i := ⟨i457.1 (by omega), i458.1 (by omega)⟩
            exact ⟨_, _, .ifLtN_true a1 (.ifLtN_true a2 (Exec.copyN (P := P) hw₂ 445 450)), le_rfl,
              fun _ => by show upd c₂.nreg 445 (c₂.nreg 450) 445 = i; rw [upd_same, g450],
              fun h' => absurd hlv h', fun r hr' => upd_other _ _ _ hr', rfl, rfl⟩
          · have hlv : ¬ Lv lb A h i := fun h' => a2 (by rw [g430]; exact i458.2 h'.2)
            exact ⟨_, _, .ifLtN_true a1 (.ifLtN_false a2 (.skip hw₂)), le_rfl,
              fun h' => absurd h' hlv, fun _ => rfl, fun _ _ => rfl, rfl, rfl⟩
        · have hlv : ¬ Lv lb A h i := fun h' => a1 (by rw [g431]; exact i457.2 h'.1)
          exact ⟨_, _, .ifLtN_false a1 (.skip hw₂), by omega, fun h' => absurd h' hlv,
            fun _ => rfl, fun _ _ => rfl, rfl, rfl⟩
      have hw₃ := e₃.wb_right
      have e₄ := Exec.addN (P := P) hw₃ 450 450 431 (by
        rw [hr₃ 450 (by omega), g450, hr₃ 431 (by omega), g431]; omega)
      set c₄ : Config := { c₃ with nreg := upd c₃.nreg 450 (c₃.nreg 450 + c₃.nreg 431) }
      have k₄ : ∀ r, r ≠ 450 → c₄.nreg r = c₃.nreg r := fun r hr' => upd_other _ _ _ hr'
      refine ⟨c₄, _, .seq e₂ (.seq e₃ e₄), ⟨e₄.wb_right, ?_, ?_, by omega, ?_, fun r a b => ?_,
        by rw [show c₄.nmem = c₃.nmem from rfl, hm₃, hm₂, hm], by
          rw [show c₄.output = c₃.output from rfl, ho₃, ho₂, ho]⟩, by omega⟩
      · show upd c₃.nreg 450 (c₃.nreg 450 + c₃.nreg 431) 450 = _
        rw [upd_same, hr₃ 450 (by omega), g450, hr₃ 431 (by omega), g431]
      · rw [k₄ 436 (by omega), hr₃ 436 (by omega), hr₂ 436 (Or.inl (by omega)), g436]
      · rintro ⟨x, hx, hlx⟩
        rw [k₄ 445 (by omega)]
        by_cases hli : Lv lb A h i
        · rw [y1 hli]; exact ⟨hlt, hli⟩
        · have hxi : x < i := by
            rcases Nat.lt_succ_iff_lt_or_eq.1 hx with h' | rfl
            · exact h'
            · exact absurd hlx hli
          rw [y2 hli, hr₂ 445 (Or.inl (by omega))]
          exact hinv ⟨x, hxi, hlx⟩
      · rw [k₄ r (by omega), hr₃ r a, hr₂ r (by omega)]; exact F r a b)
    (by omega) hI₀
  exact ⟨c', 1 + t, .seq e₀ e, by omega, hI'.2.2.2.2.1, hI'.2.2.2.2.2.1, hI'.2.2.2.2.2.2.1,
    hI'.2.2.2.2.2.2.2⟩

end XF

section Out

variable {D Q : Type*} [Fintype D] [DecidableEq D] [Fintype Q] [DecidableEq Q] {M : Map D Q}

/-- **A dart leaving the component of a face off the zone** of the low levels of a
breadth-first tree: a dart of its boundary cycle or its reversal. -/
theorem exists_out_comp (hM : M.IsPlane) {T : M.SpTree} (hT : IsBFS T) {l₂ : ℕ} (hl2 : 1 ≤ l₂)
    {f : M.Face} (hf : f ∉ M.zone (T.low l₂)) : ∃ x, Out (M.comp (T.low l₂) f) x := by
  classical
  obtain ⟨C, -, hC, -⟩ := hM.exists_scycle_comp T (root_mem_low hT hl2)
    (fun v hv => parent_mem_low hT hv) hf
  have hm := (hC (C.d 0)).not.2 (not_not.2 (C.mem_d C.pos))
  by_cases h : M.face (C.d 0) ∈ M.comp (T.low l₂) f
  · exact ⟨C.d 0, h, fun h' => hm ⟨fun _ => h', fun _ => h⟩⟩
  · refine ⟨M.α (C.d 0), ?_, ?_⟩
    · by_contra h'
      exact hm ⟨fun h'' => absurd h'' h, fun h'' => absurd h'' h'⟩
    · rw [M.α_α]; exact h

end Out

/-! ### The boundary cycle of `Y` -/

/-- **The boundary cycle of `Y`**: its label `r597` into `r437`, a dart `x₀` leaving `Y`
(`xfind`), the darts leaving `Y` by their vertices (`bdPass`) and the walk (`cyWalk`). -/
def s10cyc : Stmt := .seq (.instr (.copyN 437 597)) <| .seq xfind <| .seq bdPass cyWalk

/-- `BR` with the label and the start changed. -/
theorem BR.of2 {bA bV bL k h bNx bCy bPos n bLv bPr l x₀ u : ℕ} {c c' : Config}
    (hB : BR bA bV bL k h bNx bCy bPos n bLv bPr l x₀ u c)
    (e : ∀ r, 430 ≤ r → r < 447 → r ≠ 437 → r ≠ 445 → c'.nreg r = c.nreg r) {h' x₀' : ℕ}
    (e437 : c'.nreg 437 = h') (e445 : c'.nreg 445 = x₀') :
    BR bA bV bL k h' bNx bCy bPos n bLv bPr l x₀' u c' :=
  ⟨(e _ (by omega) (by omega) (by omega) (by omega)).trans hB.r330,
    (e _ (by omega) (by omega) (by omega) (by omega)).trans hB.r331,
    (e _ (by omega) (by omega) (by omega) (by omega)).trans hB.r332,
    (e _ (by omega) (by omega) (by omega) (by omega)).trans hB.r333,
    (e _ (by omega) (by omega) (by omega) (by omega)).trans hB.r334,
    (e _ (by omega) (by omega) (by omega) (by omega)).trans hB.r335,
    (e _ (by omega) (by omega) (by omega) (by omega)).trans hB.r336, e437,
    (e _ (by omega) (by omega) (by omega) (by omega)).trans hB.r338,
    (e _ (by omega) (by omega) (by omega) (by omega)).trans hB.r339,
    (e _ (by omega) (by omega) (by omega) (by omega)).trans hB.r340,
    (e _ (by omega) (by omega) (by omega) (by omega)).trans hB.r341,
    (e _ (by omega) (by omega) (by omega) (by omega)).trans hB.r342,
    (e _ (by omega) (by omega) (by omega) (by omega)).trans hB.r343,
    (e _ (by omega) (by omega) (by omega) (by omega)).trans hB.r344, e445,
    (e _ (by omega) (by omega) (by omega) (by omega)).trans hB.r346⟩

section Cyc

variable {D Q : Type*} [Fintype D] [DecidableEq D] [Fintype Q] [DecidableEq Q] {M : Map D Q}

set_option maxHeartbeats 8000000 in
/-- **The boundary cycle of `Y` on the machine.** With the labels at `bL` marking `Y` by the label
in `r597` and a clear array at `bNx`, `s10cyc` finds a dart `x₀` leaving `Y` (in `r445`) and
writes the darts of `bdCycle Y x₀` at `bCy` (their number in `r451`) and the position of each of
its vertices at `bPos`, within `180 k + 12` steps. -/
theorem s10cyc_spec {T : M.SpTree} {k n : ℕ} {cd : D ≃ Fin (3 * k)} {vi : Q ≃ Fin n}
    {A V : ℕ → ℕ} {W : ℕ} {P : Input} {c : Config}
    {bV bL h₀ bNx bCy bPos bLv bPr l x₀' u l₂ : ℕ} {δ : D}
    (hM : M.IsPlane) (hT : IsBFS T) (hl2 : 1 ≤ l₂)
    (hAcd : ∀ x, A (cd x) = cd (M.α x)) (hV : ∀ x, V (cd x) = vi (M.vert x))
    (hz1 : M.face δ ∉ M.zone (T.low l₂))
    (hlay : 3 * k ≤ bNx ∧ bV + 3 * k ≤ bNx ∧ bNx + n ≤ bL ∧ bL + k ≤ bCy ∧ bCy + 3 * k ≤ bPos ∧
      bPos + n ≤ W)
    (hc : WordsBounded W c) (hB : BR 0 bV bL k h₀ bNx bCy bPos n bLv bPr l x₀' u c)
    (mA : ∀ x < 3 * k, c.nmem x = A x) (mV : ∀ x < 3 * k, c.nmem (bV + x) = V x)
    (hlab : ∀ y : D, c.nmem (bL + (cd y : ℕ) / 3) = c.nreg 597 ↔
      M.face y ∈ M.comp (T.low l₂) (M.face δ))
    (hNx : ∀ v < n, c.nmem (bNx + v) = 0) :
    ∃ c' t, Exec P W s10cyc c c' t ∧ t ≤ 180 * k + 12 ∧
      ∃ (x₀ : D) (hok : BdOK (M.comp (T.low l₂) (M.face δ)) x₀), (cd x₀ : ℕ) = c'.nreg 445 ∧
        c'.nreg 451 = (bdCycle _ x₀ hok).k ∧
        (∀ i < (bdCycle _ x₀ hok).k, c'.nmem (bCy + i) = cd ((bdCycle _ x₀ hok).d i)) ∧
        (∀ i < (bdCycle _ x₀ hok).k,
          c'.nmem (bPos + vi (M.vert ((bdCycle _ x₀ hok).d i))) = i) ∧
        (∀ a, (a < bNx ∨ bNx + n ≤ a) → ¬ (bCy ≤ a ∧ a < bCy + 3 * k) →
          ¬ (bPos ≤ a ∧ a < bPos + n) → c'.nmem a = c.nmem a) ∧
        (∀ r, r ≠ 437 → r ≠ 445 → (r < 450 ∨ 466 ≤ r) → c'.nreg r = c.nreg r) ∧
        c'.output = c.output := by
  classical
  obtain ⟨l1, l2, l3, l4, l5, l6⟩ := hlay
  set Y := M.comp (T.low l₂) (M.face δ)
  set lb : ℕ → ℕ := fun g => c.nmem (bL + g)
  have hk : 0 < k := by have := (cd δ).2; omega
  have hA' : ∀ x < 3 * k, c.nmem (0 + x) = A x ∧ A x < 3 * k := fun x hx => by
    refine ⟨by rw [zero_add]; exact mA x hx, ?_⟩
    have e : x = cd (cd.symm ⟨x, hx⟩) := by simp
    rw [e, hAcd]; exact (cd _).2
  have hV' : ∀ x < 3 * k, c.nmem (bV + x) = V x ∧ V x < n := fun x hx => by
    refine ⟨mV x hx, ?_⟩
    have e : x = cd (cd.symm ⟨x, hx⟩) := by simp
    rw [e, hV]; exact (vi _).2
  -- 0. the label
  have e₁ := Exec.copyN (P := P) hc 437 597
  set c₁ : Config := { c with nreg := upd c.nreg 437 (c.nreg 597) }
  have k₁ : ∀ r, r ≠ 437 → c₁.nreg r = c.nreg r := fun r hr => upd_other _ _ _ hr
  have hw₁ := e₁.wb_right
  set h := c.nreg 597
  have hl : ∀ y : D, lb ((cd y : ℕ) / 3) = h ↔ M.face y ∈ Y := hlab
  have hlv : ∀ y : D, Lv lb A h (cd y) ↔ Out Y y := lv_iff_out cd hAcd hl
  -- 1. a dart leaving `Y`
  obtain ⟨c₂, t₂, e₂, ht₂, hx₂, hr₂, hm₂, ho₂⟩ := xfind_exec (P := P) (A := A) (lb := lb)
    (k := k) (h := h) (bA := 0) (bL := bL) ⟨by omega, by omega⟩ c₁ hw₁
    ((k₁ 430 (by omega)).trans hB.r330) ((k₁ 431 (by omega)).trans hB.r331)
    ((k₁ 432 (by omega)).trans hB.r332) ((k₁ 433 (by omega)).trans hB.r333)
    ((k₁ 435 (by omega)).trans hB.r335) ((k₁ 436 (by omega)).trans hB.r336)
    (by show upd c.nreg 437 (c.nreg 597) 437 = h; rw [upd_same]) hA' (fun g _ => rfl)
  obtain ⟨y, hy⟩ := exists_out_comp hM hT hl2 hz1
  obtain ⟨hx0, hx0l⟩ := hx₂ ⟨cd y, (cd y).2, (hlv y).2 hy⟩
  set x₀ : D := cd.symm ⟨c₂.nreg 445, hx0⟩
  have ex₀ : (cd x₀ : ℕ) = c₂.nreg 445 := by simp [x₀]
  have hout : Out Y x₀ := (hlv x₀).1 (by rw [ex₀]; exact hx0l)
  obtain ⟨C, hCp, hC, -⟩ := hM.exists_scycle_comp T (root_mem_low hT hl2)
    (fun v hv => parent_mem_low hT hv) hz1
  have hok : BdOK Y x₀ := ⟨⟨C, hCp, hC⟩, hout⟩
  have hw₂ := e₂.wb_right
  have hB₂ : BR 0 bV bL k h bNx bCy bPos n bLv bPr l (c₂.nreg 445) u c₂ :=
    BR.of2 hB (fun r a b d e => by rw [hr₂ r e (Or.inl (by omega)), k₁ r d])
      (by rw [hr₂ 437 (by omega) (Or.inl (by omega))]; show upd c.nreg 437 (c.nreg 597) 437 = h
          rw [upd_same]) rfl
  have fm₂ : c₂.nmem = c.nmem := hm₂
  -- 2. the darts leaving `Y`
  obtain ⟨c₃, t₃, e₃, ht₃, hPI, h451, hm₃, hr₃, ho₃⟩ := bdPass_exec (P := P) (A := A) (lb := lb)
    (V := V) ⟨by omega, by omega, l3⟩ (by omega) c₂ hw₂ hB₂ (by rw [fm₂]; exact hA')
    (fun g _ => by rw [fm₂]) (by rw [fm₂]; exact hV')
  have hw₃ := e₃.wb_right
  set NX : ℕ → ℕ := fun v => c₃.nmem (bNx + v)
  have hP : ∀ v < n, (∃ x < 3 * k, Lv lb A h x ∧ V x = v) →
      ∃ x < 3 * k, Lv lb A h x ∧ V x = v ∧ NX v = x := fun v hv hex => by
    obtain ⟨x, hx, h1, h2, h3⟩ := (hPI v hv).1 hex
    exact ⟨x, hx, h1, h2, h3⟩
  have hN : ∀ v < n, NX v < 3 * k := fun v hv => by
    by_cases hex : ∃ x < 3 * k, Lv lb A h x ∧ V x = v
    · obtain ⟨x, hx, -, -, h3⟩ := hP v hv hex
      rw [h3]; exact hx
    · show c₃.nmem (bNx + v) < 3 * k
      rw [(hPI v hv).2 hex, fm₂, hNx v hv]; omega
  have hK : bdK Y ≤ 3 * k := by
    unfold bdK
    exact (card_le_univ _).trans (by rw [Fintype.card_congr cd, Fintype.card_fin])
  have hB₃ : BR 0 bV bL k h bNx bCy bPos n bLv bPr l (c₂.nreg 445) u c₃ :=
    hB₂.of fun r a b => hr₃ r (Or.inl (by omega))
  obtain ⟨c₄, t₄, e₄, ht₄, hcy, hpos, -, hm₄, hr₄, ho₄⟩ := cyWalk_exec (P := P) (A := A) (V := V)
    (NX := NX) (K := bdK Y) ⟨by omega, by omega, by omega, by omega⟩ l6 c₃ hw₃ hB₃
    (by rw [h451, nOut_eq_bdK cd hlv]) hx0 (fun x hx => by rw [hm₃ _ (Or.inl (by omega)), fm₂]; exact hA' x hx)
    (fun x hx => by rw [hm₃ _ (Or.inl (by omega)), fm₂]; exact hV' x hx)
    (fun v hv => ⟨rfl, hN v hv⟩)
    (by rw [← ex₀]; exact cyNext_inj cd vi hAcd hV hlv hN hP hok)
  have hit : ∀ i, (cyNext A V NX)^[i] (c₂.nreg 445) = cd (bdD Y x₀ i) := fun i => by
    rw [← ex₀]; exact cyNext_iter_bdD cd vi hAcd hV hlv hN hP hok i
  refine ⟨c₄, 1 + (t₂ + (t₃ + t₄)), .seq e₁ (.seq e₂ (.seq e₃ e₄)), by omega, x₀, hok, ?_,
    ?_, fun i hi => ?_, fun i hi => ?_, fun a h1 h2 h3 => ?_, fun r a b d => ?_, ?_⟩
  · rw [ex₀, hr₄ 445 (Or.inl (by omega)), hr₃ 445 (Or.inl (by omega))]
  · rw [hr₄ 451 (Or.inl (by omega)), h451, nOut_eq_bdK cd hlv, bdCycle_k]
  · rw [bdCycle_k] at hi
    rw [hcy i hi, hit, bdCycle_d]
  · rw [bdCycle_k] at hi
    have := hpos i hi
    rw [hit, hV] at this
    rw [bdCycle_d]; exact this
  · rw [hm₄ a (fun h' => h2 ⟨h'.1, by omega⟩) h3, hm₃ a h1, fm₂]
  · rw [hr₄ r (by omega), hr₃ r (by omega), hr₂ r b (by omega), k₁ r a]
  · rw [ho₄, ho₃, ho₂]

end Cyc

/-! ### The fallback of the deep case -/

section Fallback

variable {D Q : Type*} [Fintype D] [DecidableEq D] [Fintype Q] [DecidableEq Q] {M : Map D Q}

open Classical in
/-- **The fallback of the deep case, explicitly.** In the deep case, with a dart `x₀` leaving
`Y` (as found by `s10cyc`), if the ancestors at level `l₂` of the ends of `δ` coincide (the test
of `s9top`) or `Y` weighs at least `1/3` (the test `r168 ≤ 3 r599` of `s10hvy`), the explicit
separator is the boundary cycle of `Y` (written by `s10cyc`) with `Y` (the faces of label `r597`),
and it is a separator. -/
theorem deep_fallback_sep (hM : M.IsPlane) (htri : ∀ δ : D, M.IsTriangle δ) {T : M.SpTree}
    (hT : IsBFS T) {w : Q → ℝ} (hw : ∀ v, 0 ≤ w v) (h1 : ∑ v, w v ≤ 1) {l₀ l₂ : ℕ}
    {H : Finset M.Face} {K₀ : Finset Q} {c₀ : Q} {T₁ : M.SpTree} (hI : Inner T w l₀ H K₀ c₀ T₁)
    (hl : l₀ < l₂) {cn : Q → Q} (hcn : IsConc T l₂ cn) {δ : D} (hδ : ¬ T₁.IsTree δ)
    (hA : ∑ v ∈ T₁.inC δ, wcf cn w v ≤ 2 / 3) (hB : ∑ v ∈ T₁.outC δ, wcf cn w v ≤ 2 / 3)
    (hlight : ∀ f, f ∉ M.zone (T.low l₂) → ∑ v ∈ ins (M.comp (T.low l₂) f), w v ≤ 2 / 3)
    (hz1 : M.face δ ∉ M.zone (T.low l₂)) (hz2 : M.face (M.α δ) ∉ M.zone (T.low l₂)) {x₀ : D}
    (hok : BdOK (M.comp (T.low l₂) (M.face δ)) x₀) {g₀ : M.Face}
    (hfb : topA T T₁ l₂ (M.vert δ) = topA T T₁ l₂ (M.vert (M.α δ)) ∨
      1 / 3 ≤ ∑ v ∈ ins (M.comp (T.low l₂) (M.face δ)), w v) :
    bandSep T T₁ l₂ cn w δ x₀ g₀ =
        (bdCycle _ x₀ hok, M.comp (T.low l₂) (M.face δ)) ∧
      (∀ g₁, g₁ ∈ M.zone (T.low l₂) →
        SepOK w (2 * (l₂ - l₀) + #K₀ + #(T.lvl l₂))
          (bdCycle _ x₀ hok, M.comp (T.low l₂) (M.face δ))) := by
  have e : bandSep T T₁ l₂ cn w δ x₀ g₀ =
      (bdCycle _ x₀ hok, M.comp (T.low l₂) (M.face δ)) := by
    rw [bandSep_of_deep hz1 hz2 hok, deepSep, ite_eq_left_of_eq_true _ _ (eq_true hfb)]
  refine ⟨e, fun g₁ hg₁ => ?_⟩
  have := band_separator_explicit hM htri hT hw h1 hI hl hcn hδ hA hB hlight (x₀ := x₀)
    (fun _ _ => hok.2) hg₁
  rwa [bandSep_of_deep hz1 hz2 hok, deepSep, ite_eq_left_of_eq_true _ _ (eq_true hfb)] at this

end Fallback

end MillerProg

end PlanarSeparator
