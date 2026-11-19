module

public import PlanarSeparator.Machine.MillerJump
public import PlanarSeparator.Machine.MillerConc

/-!
# Miller's separator on the machine: step 8 from the parent darts

One program for step 8 of `PlanarSeparator/Machine/Miller.lean`, from the coded triangulation (the
reversals at `x`, the vertices of the darts at `bV`), the parent darts of a spanning tree `T` (at
`bPr`) and natural vertex weights (at `bW`):

`step8run = tmpass ; search ; upass ; lgprog ; tbuild ; jpass ; step8`

(the tree marks and clear face marks, the search of the dual tree, the parents, `L`, the table of
ancestors, the depths and root sums by pointer jumping, and step 8). **`step8run_tree`**: within

`(125 log₂ n + 564) k + (39 n + 122) log₂ n + 94 n + 468`

steps, `r353` is the number of a dart `δ` off the tree whose strict inside and strict outside each
weigh at most `2/3` of the total weight (the conclusion of
`PlanarSeparator.Map.SpTree.exists_simple_balanced`), for any spanning tree `T` given by its
parent darts: in particular for the tree `T₁` of the inner region (step 6).

Layout: the reversals at `[0, 3k)` (`bR = 0`), the Lipton–Tarjan arrays in `[3k, 11k)`, and above
`11 k`: `bV < bPr < bU < bW < bD < bS < bD₂ < bS₂` (the table of `L ≤ log₂ n + 1` levels at `bU`).
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false

namespace PlanarSeparator

namespace MillerProg

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs Finset CycleSearch

/-- **Step 8 from the parent darts.** -/
def step8run : Stmt :=
  .seq tmpass <| .seq search <| .seq upass <| .seq lgprog <| .seq tbuild <| .seq jpass step8

/-- The state of the search survives programs that keep `r0 … r12` and the memory below `11 k`. -/
theorem SB.keep11 {k : ℕ} {A Tm Fw : ℕ → ℕ} {W : ℕ} {o : List ℕ} {c c' : Config}
    (h : SB k A Tm Fw W o c) (hw : WordsBounded W c') (hr : ∀ r ≤ 12, c'.nreg r = c.nreg r)
    (hm : ∀ a < 11 * k, c'.nmem a = c.nmem a) (ho : c'.output = c.output) :
    SB k A Tm Fw W o c' := by
  have tl := h.tail_le
  have hq : ∀ i < k, qu k c'.nmem i = qu k c.nmem i := fun i hi => hm _ (by omega)
  have hp : ∀ f < k, pd k c'.nmem f = pd k c.nmem f := fun f hf => hm _ (by omega)
  have hmk : ∀ f < k, mark k c'.nmem f = mark k c.nmem f := fun f hf => hm _ (by omega)
  have r11 := hr 11 (by omega)
  have r12 := hr 12 (by omega)
  refine ⟨hw, cregs_of h.regs fun r hr' => hr r (by omega), ⟨fun x hx => ?_, fun x hx => ?_,
    fun f hf => ?_⟩, ho.trans h.out, ?_, fun i hi => ?_, fun i hi j hj e => ?_, ?_,
    fun f hf => ?_, fun f hf => ?_, fun i h1 hi => ?_⟩
  · rw [hm _ (by omega)]; exact h.hold.1 x hx
  · rw [hm _ (by omega)]; exact h.hold.2.1 x hx
  · rw [hm _ (by omega)]; exact h.hold.2.2 f hf
  · rw [r11, r12]; exact h.head_le
  · rw [r11] at hi; rw [hq i (by omega)]; exact h.q_lt i hi
  · rw [r11] at hi hj; rw [hq i (by omega), hq j (by omega)] at e; exact h.q_inj i hi j hj e
  · rw [r11, hq 0 (by have := h.q0.1; omega)]; exact h.q0
  · rw [hmk f hf]; exact h.mk01 f hf
  · rw [hmk f hf, r11]
    refine (h.mk_iff f hf).trans ⟨fun ⟨i, hi, e⟩ => ⟨i, hi, by rw [hq i (by omega)]; exact e⟩,
      fun ⟨i, hi, e⟩ => ⟨i, hi, by rw [← hq i (by omega)]; exact e⟩⟩
  · rw [r11] at hi
    have hqi := h.q_lt i hi
    rw [hq i (by omega), hp _ hqi]
    obtain ⟨a1, a2, a3, i', hi', e⟩ := h.pd_ok i h1 hi
    exact ⟨a1, a2, a3, i', hi', by rw [hq i' (by omega)]; exact e⟩

set_option maxHeartbeats 8000000 in
/-- **Step 8 from the parent darts on the machine.** Let `M` be a plane triangulation with `k ≥ 2`
faces coded by `cd` (reversals `A` at `x`, face permutation `phi3`, vertices `V` at `bV`, read through
a numbering `vi` of the `n` vertices), `T` a spanning tree whose parent darts are at `bPr`, and
`wv` natural vertex weights (at `bW`). From a state with the constant registers set, within
`(125 log₂ n + 564) k + (39 n + 122) log₂ n + 94 n + 468` steps, `step8run` leaves in `r353` the
number of a dart `δ` off the tree whose strict inside and strict outside weigh at most `2/3` of
the total. -/
theorem step8run_tree {D Q : Type*} [Fintype D] [DecidableEq D] [Fintype Q] [DecidableEq Q]
    {M : Map D Q} {T : M.SpTree} {k n : ℕ} {cd : D ≃ Fin (3 * k)} {vi : Q ≃ Fin n}
    {A V w : ℕ → ℕ} (wv : Q → ℕ) {W : ℕ} {P : Input} {c : Config}
    {bV bPr bU bW bD bS bD₂ bS₂ : ℕ}
    (hM : M.IsPlane) (hT3 : ∀ δ, M.IsTriangle δ) (hk2 : 2 ≤ k)
    (hAcd : ∀ x, A (cd x) = cd (M.α x)) (hφ : ∀ x, (cd (M.φ x) : ℕ) = phi3 (cd x))
    (hV : ∀ x, V (cd x) = vi (M.vert x)) (hw : ∀ x, w (vi x) = wv x)
    (hlay : 11 * k ≤ bV ∧ bV + 3 * k ≤ bPr ∧ bPr + n ≤ bU ∧
      bU + (Nat.log 2 n + 1) * n ≤ bW ∧ bW + n ≤ bD ∧ bD + n ≤ bS ∧ bS + n ≤ bD₂ ∧
      bD₂ + n ≤ bS₂ ∧ bS₂ + n ≤ W)
    (hWt : 11 * k + 3 * ∑ v, wv v + 4 ≤ W)
    (hc : WordsBounded W c) (hR : CRegs k c) (h140 : c.nreg 140 = 0) (h141 : c.nreg 141 = 1)
    (h147 : c.nreg 147 = 0) (h161 : c.nreg 161 = n) (h162 : c.nreg 162 = bV)
    (h215 : c.nreg 215 = bPr) (h250 : c.nreg 250 = bW) (h252 : c.nreg 252 = bS)
    (h253 : c.nreg 253 = bD) (h254 : c.nreg 254 = bU) (h255 : c.nreg 255 = vi T.root)
    (h381 : c.nreg 381 = bD₂) (h382 : c.nreg 382 = bS₂)
    (mA : ∀ x < 3 * k, c.nmem x = A x) (mV : ∀ x < 3 * k, c.nmem (bV + x) = V x)
    (mW : ∀ u < n, c.nmem (bW + u) = w u)
    (hPr : ∀ v (h : v ≠ T.root), c.nmem (bPr + vi v) = cd (T.par v h)) :
    ∃ c' t, Exec P W step8run c c' t ∧
      t ≤ (125 * Nat.log 2 n + 564) * k + (39 * n + 122) * Nat.log 2 n + 94 * n + 468 ∧
      (∀ a, 11 * k ≤ a → (a < bU ∨ bU + (Nat.log 2 n + 1) * n ≤ a) → (a < bD ∨ bS₂ + n ≤ a) →
        c'.nmem a = c.nmem a) ∧ (∀ x < 3 * k, c'.nmem x = A x) ∧
      ∃ δ : D, (cd δ : ℕ) = c'.nreg 353 ∧ ¬ T.IsTree δ ∧
        3 * ∑ v ∈ T.inC δ, wv v ≤ 2 * ∑ v, wv v ∧ 3 * ∑ v ∈ T.outC δ, wv v ≤ 2 * ∑ v, wv v := by
  classical
  obtain ⟨l0, l1, l2, l3, l4, l5, l6, l7, l8⟩ := hlay
  have hk : 0 < k := by omega
  have hn : 0 < n := by have := (vi T.root).2; omega
  set r₀ := (vi T.root : ℕ)
  set Pr : ℕ → ℕ := fun u => c.nmem (bPr + u)
  have hPr' : ∀ v (h : v ≠ T.root), Pr (vi v) = cd (T.par v h) := hPr
  have hin := rootIn_tree cd vi T hAcd hV hPr'
  set f := upN A V Pr r₀
  have hf : ∀ x, f (vi x) = vi (T.parent x) := upN_tree cd vi T hAcd hV hPr'
  have htot : ∀ X : Finset Q, ∑ v ∈ X, wv v ≤ W := fun X =>
    (sum_le_sum_of_subset (subset_univ X)).trans (by omega)
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hR
  -- 1. the tree marks
  have hTF : TFix k n r₀ bPr W A Pr c :=
    ⟨⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩, h161, h215, h255, mA, hin.A_lt,
      fun v _ _ => rfl, hin.Pr_lt, by omega, by omega, by omega⟩
  obtain ⟨c₁, t₁, e₁, ht₁, hT₁, hz₁, hm₁, hr₁, ho₁⟩ := tmpass_exec (P := P) hTF hc
  have hC := coded_of_tmark (k := k) (cd := cd) (vi := vi) (A := A) (Pr := Pr) hAcd hφ hPr'
  set Tm := tmark A Pr r₀ n
  have hw₁ := e₁.wb_right
  have fr₁ : ∀ r, r < 370 ∨ 373 < r → c₁.nreg r = c.nreg r := fun r hr =>
    hr₁ r (by omega) (by omega) (by omega) (by omega)
  have mm₁ : ∀ a, a < 3 * k ∨ (6 * k ≤ a ∧ a < 7 * k) ∨ 8 * k ≤ a → c₁.nmem a = c.nmem a :=
    fun a ha => hm₁ a (by unfold TOut; omega)
  -- 2. the search
  have hH₁ : Holds k A Tm (fun f => c₁.nmem (6 * k + f)) c₁.nmem :=
    ⟨fun x hx => by rw [mm₁ x (by omega)]; exact mA x hx, fun x hx => hT₁ x hx, fun _ _ => rfl⟩
  obtain ⟨c₂, t₂, e₂, hI₂, hend₂, ht₂, hm₂⟩ := search_exec (P := P) (o := c₁.output) hC.tri
    (by omega) hk c₁ hw₁ (cregs_of ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
      fun r hr => fr₁ r (by omega)) hH₁ rfl hz₁
  have hall₂ := hC.search_all hM hk hI₂ hend₂
  have hw₂ := e₂.wb_right
  have fr₂ : ∀ r, 25 ≤ r → c₂.nreg r = c₁.nreg r := fun r hr =>
    e₂.nreg_of_wr (Stmt.wr_of_wmax (by have hs : search.wmax < 25 := (by decide); omega))
  have g : ∀ r, 25 ≤ r → (r < 370 ∨ 373 < r) → c₂.nreg r = c.nreg r := fun r a b => by
    rw [fr₂ r a, fr₁ r b]
  have mm₂ : ∀ a, 11 * k ≤ a → c₂.nmem a = c.nmem a := fun a ha => by
    rw [hm₂ a ha, mm₁ a (by omega)]
  -- 3. the parents
  obtain ⟨c₃, t₃, e₃, ht₃, hU₃, hr₃, hm₃, ho₃⟩ := upass_exec (P := P) (bR := 0) hin
    ⟨by omega, by omega, l2, by omega⟩ c₂ hw₂ ((g 140 (by omega) (by omega)).trans h140)
    ((g 141 (by omega) (by omega)).trans h141) ((g 147 (by omega) (by omega)).trans h147)
    ((g 161 (by omega) (by omega)).trans h161) ((g 162 (by omega) (by omega)).trans h162)
    ((g 215 (by omega) (by omega)).trans h215) ((g 254 (by omega) (by omega)).trans h254)
    ((g 255 (by omega) (by omega)).trans h255)
    (fun x hx => by rw [zero_add]; exact hI₂.hold.1 x hx)
    (fun x hx => by rw [mm₂ _ (by omega)]; exact mV x hx)
    (fun v hv _ => by rw [mm₂ _ (by omega)])
  have hw₃ := e₃.wb_right
  -- 4. the number of levels
  obtain ⟨c₄, t₄, e₄, ht₄, hL1, hnL, hLl, hr₄, hm₄, ho₄⟩ := lgprog_exec (P := P) (n := n)
    (W := W) (by omega) c₃ hw₃
    ((hr₃ 141 (by omega) (by omega) (by omega)).trans ((g 141 (by omega) (by omega)).trans h141))
    ((hr₃ 161 (by omega) (by omega) (by omega)).trans ((g 161 (by omega) (by omega)).trans h161))
  set L := c₄.nreg 271
  have hw₄ := e₄.wb_right
  have hLn : L * n ≤ (Nat.log 2 n + 1) * n := Nat.mul_le_mul_right _ hLl
  have g₄ : ∀ r, 25 ≤ r → (r < 370 ∨ 373 < r) → r ≠ 270 → r ≠ 271 → r ≠ 380 → r ≠ 385 →
      r ≠ 386 → c₄.nreg r = c.nreg r := fun r a b d e f' g' h' => by
    rw [hr₄ r d e, hr₃ r f' g' h', g r a b]
  -- 5. the table
  have hfl : ∀ v < n, f v < n := fun v hv => hin.up_lt hv
  obtain ⟨c₅, t₅, e₅, ht₅, hTab, hr₅, hm₅, ho₅⟩ := tbuild_exec (P := P) (W := W) (n := n)
    (bU := bU) (L := L) (f := f) (by omega) hfl (by omega) hL1 c₄ hw₄
    ((g₄ 140 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).trans h140)
    ((g₄ 141 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).trans h141)
    ((g₄ 161 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).trans h161)
    ((g₄ 254 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).trans h254)
    rfl (fun v hv => by rw [hm₄, hU₃ v hv])
  have hw₅ := e₅.wb_right
  have g₅ : ∀ r, 279 ≤ r → (r < 370 ∨ 373 < r) → r ≠ 380 → r ≠ 385 → r ≠ 386 →
      c₅.nreg r = c.nreg r := fun r a b d e f' => by
    rw [hr₅ r (by omega)]; exact g₄ r (by omega) b (by omega) (by omega) d e f'
  have g₅' : ∀ r, 25 ≤ r → r < 270 → c₅.nreg r = c.nreg r := fun r a b => by
    rw [hr₅ r (by omega)]
    exact g₄ r a (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have hnLn : n ≤ L * n := Nat.le_mul_of_pos_left n hL1
  have mm₅ : ∀ a, 11 * k ≤ a → (a < bU ∨ bU + L * n ≤ a) → c₅.nmem a = c.nmem a := fun a ha hb => by
    rw [hm₅ a (by omega), hm₄, hm₃ a (by omega), mm₂ a ha]
  -- 6. the depths and the root sums
  have hJF : JFix n r₀ bW bS bD bU L bD₂ bS₂ W f w c₅ :=
    { r140 := (g₅' 140 (by omega) (by omega)).trans h140
      r141 := (g₅' 141 (by omega) (by omega)).trans h141
      r161 := (g₅' 161 (by omega) (by omega)).trans h161
      r250 := (g₅' 250 (by omega) (by omega)).trans h250
      r252 := (g₅' 252 (by omega) (by omega)).trans h252
      r253 := (g₅' 253 (by omega) (by omega)).trans h253
      r254 := (g₅' 254 (by omega) (by omega)).trans h254
      r255 := (g₅' 255 (by omega) (by omega)).trans h255
      r271 := by rw [hr₅ 271 (by omega)]
      r381 := (g₅ 381 (by omega) (by omega) (by omega) (by omega) (by omega)).trans h381
      r382 := (g₅ 382 (by omega) (by omega) (by omega) (by omega) (by omega)).trans h382
      tab := hTab
      mW := fun v hv => by rw [mm₅ _ (by omega) (Or.inr (by omega))]; exact mW v hv
      r₀_lt := (vi T.root).2
      f_lt := hfl
      hL := hL1
      l1 := by omega
      l2 := l4
      l3 := l5
      l4 := l6
      l5 := l7
      l6 := l8
      hDW := fun v hv => by
        obtain ⟨x, rfl⟩ := exists_vi vi hv
        rw [Dj_tree vi T hf hnL]
        have := card_anc_le vi T x; omega
      hSW := fun v hv => by
        obtain ⟨x, rfl⟩ := exists_vi vi hv
        rw [Sj_tree vi T wv hf hw hnL]; exact htot _ }
  obtain ⟨c₆, t₆, e₆, ht₆, hd₆, hr₆, hm₆, ho₆⟩ := jpass_tree vi T wv hf hw hnL (P' := P) hJF hw₅
  have hw₆ := e₆.wb_right
  have g₆ : ∀ r, 25 ≤ r → r < 270 → c₆.nreg r = c.nreg r := fun r a b => by
    rw [hr₆.get (by omega)]; exact g₅' r a b
  -- 7. step 8
  set R : ℕ → ℕ := fun u => c₆.nmem (bS + u)
  set dep : ℕ → ℕ := fun u => c₆.nmem (bD + u)
  have hTr : PTree n r₀ f dep := ptree_tree vi T hf (fun x => (hd₆ x).1)
  have hS₆ : SB k A Tm (fun f => c₁.nmem (6 * k + f)) W c₁.output c₆ :=
    SB.keep11 hI₂.toSB hw₆ (fun r hr => by
      rw [hr₆ r (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega), hr₅ r (by omega), hr₄ r (by omega) (by omega), hr₃ r (by omega) (by omega)
        (by omega)])
      (fun a ha => by rw [hm₆ a (Or.inl (by omega)), hm₅ a (Or.inl (by omega)), hm₄,
        hm₃ a (Or.inl (by omega))])
      (by rw [ho₆, ho₅, ho₄, ho₃])
  have hall₆ : c₆.nreg 11 = k := by
    rw [hr₆ 11 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega), hr₅ 11 (by omega), hr₄ 11 (by omega) (by omega),
      hr₃ 11 (by omega) (by omega) (by omega)]; exact hall₂
  have mm₆ : ∀ a, 11 * k ≤ a → (a < bU ∨ bU + L * n ≤ a) → a < bD → c₆.nmem a = c.nmem a :=
    fun a ha hb hc' => by rw [hm₆ a (Or.inl hc'), mm₅ a ha hb]
  have hB : BSFix k n bV bS bW W A V R w (pd k c₆.nmem) c₆ :=
    { regs := hS₆.regs
      r162 := (g₆ 162 (by omega) (by omega)).trans h162
      r250 := (g₆ 250 (by omega) (by omega)).trans h250
      r252 := (g₆ 252 (by omega) (by omega)).trans h252
      mA := fun x hx => hS₆.hold.1 x hx
      A_lt := hin.A_lt
      mV := fun x hx => by rw [mm₆ _ (by omega) (Or.inl (by omega)) (by omega)]; exact mV x hx
      V_lt := hin.V_lt
      mP := fun F _ _ => rfl
      P_ok := fun F h1 hF => ⟨(SB.pd_face hS₆ hall₆ h1 hF).1, (SB.pd_face hS₆ hall₆ h1 hF).2.1⟩
      mS := fun v _ => rfl
      mW := fun v hv => by
        rw [mm₆ _ (by omega) (Or.inr (by omega)) (by omega)]; exact mW v hv
      lV := by omega
      lS := by omega
      lW := by omega
      hV := by omega
      hS := by omega
      hW := by omega
      hk := by omega }
  have hQ : QFix n r₀ bD bU L W f dep c₆ :=
    { r140 := (g₆ 140 (by omega) (by omega)).trans h140
      r141 := (g₆ 141 (by omega) (by omega)).trans h141
      r161 := (g₆ 161 (by omega) (by omega)).trans h161
      r253 := (g₆ 253 (by omega) (by omega)).trans h253
      r254 := (g₆ 254 (by omega) (by omega)).trans h254
      r271 := by rw [hr₆.get (by omega), hr₅ 271 (by omega)]
      tree := hTr
      tab := fun j hj v hv => by
        have : j * n + n ≤ L * n := by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hj
        rw [hm₆ _ (Or.inl (by omega))]; exact hTab j hj v hv
      mdep := fun v _ => rfl
      pow := hnL
      hL := hL1
      hU := by omega
      hD := by omega }
  obtain ⟨c₇, t₇, e₇, ht₇, -, hf₇, hl₇, δ, hδ, hnt, hin', hout'⟩ := step8_tree (P := P) wv hM hT3 hC hk2 hS₆
    hall₆ hB hQ ⟨by omega, by omega, by omega, by omega, by omega⟩ hV hf
    (fun x => (hd₆ x).2) hw hWt
  refine ⟨c₇, t₁ + (t₂ + (t₃ + (t₄ + (t₅ + (t₆ + t₇))))),
    .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ (.seq e₅ (.seq e₆ e₇))))), ?_, fun a h11 hU hD => ?_,
    fun x hx => by rw [hl₇ x hx]; exact hS₆.hold.1 x hx, δ, hδ, hnt, hin', hout'⟩
  swap
  · rw [hf₇ a h11, hm₆ a hD, hm₅ a (by omega), hm₄, hm₃ a (by omega), mm₂ a h11]
  -- the cost
  set lg := Nat.log 2 n
  have a1 : (125 * L + 347) * k ≤ (125 * (lg + 1) + 347) * k :=
    Nat.mul_le_mul_right _ (by omega)
  have a2 : (9 * n + 8) * L ≤ (9 * n + 8) * (lg + 1) := Nat.mul_le_mul_left _ hLl
  have a3 : (30 * n + 10) * L ≤ (30 * n + 10) * (lg + 1) := Nat.mul_le_mul_left _ hLl
  have b1 : (125 * (lg + 1) + 347) * k = 125 * (lg * k) + 472 * k := by ring
  have b2 : (9 * n + 8) * (lg + 1) = 9 * (n * lg) + 8 * lg + 9 * n + 8 := by ring
  have b3 : (30 * n + 10) * (lg + 1) = 30 * (n * lg) + 10 * lg + 30 * n + 10 := by ring
  have b4 : (125 * lg + 564) * k + (39 * n + 122) * lg =
      125 * (lg * k) + 564 * k + 39 * (n * lg) + 122 * lg := by ring
  have hLlg : 100 * L ≤ 100 * (lg + 1) := by omega
  omega


/-! ### With the concentrated weights -/

/-- **From natural weights to the normalized moved weights.** If the moved weights `wcf cn (wR wP)`
are the natural numbers `wv` divided by the total of `wP`, a set weighing at most `2/3` of the
total of `wv` weighs at most `2/3` for the moved weights. -/
theorem le_two_thirds_wcf {Q : Type*} [Fintype Q] [DecidableEq Q] {cn : Q → Q} {wP wv : Q → ℕ}
    (hpos : 0 < ∑ v, wP v) (h : ∀ u, Map.wcf cn (wR wP) u = (wv u : ℝ) / ∑ v, (wP v : ℝ))
    {X : Finset Q} (hX : 3 * ∑ v ∈ X, wv v ≤ 2 * ∑ v, wv v) :
    ∑ v ∈ X, Map.wcf cn (wR wP) v ≤ 2 / 3 := by
  have hS : (0 : ℝ) < ∑ v, (wP v : ℝ) := by exact_mod_cast hpos
  have htot : (∑ v, (wv v : ℝ)) = ∑ v, (wP v : ℝ) := by
    have e := Map.sum_wcf cn (wR wP)
    have e1 : ∑ v, wR wP v = 1 := by
      unfold wR; rw [← sum_div, div_self hS.ne']
    simp only [h, ← sum_div] at e
    rw [e1, div_eq_one_iff_eq hS.ne'] at e
    exact e
  have hX' : 3 * (∑ v ∈ X, (wv v : ℝ)) ≤ 2 * ∑ v, (wv v : ℝ) := by exact_mod_cast hX
  simp only [h, ← sum_div]
  rw [div_le_iff₀ hS]
  linarith

/-- **Step 8 for the redirected tree and the concentrated weights.** Let `T₁` be a spanning tree
(the tree of the inner region, `iprog_inner`) with its parent darts at `bPr`, and the natural
weights at `bWC` the moved weights of a concentration `cn` (`conc_exec`: the normalized moved
weights `wcf cn (wR wP)` are these numbers divided by the total of `wP`). Then `step8run` finds a
dart `δ` off `T₁` whose strict inside and strict outside weigh at most `2/3` for the moved weights:
the hypotheses `hA`, `hB` of `PlanarSeparator.Map.band_separator_of_dart`. -/
theorem step8run_conc {D Q : Type*} [Fintype D] [DecidableEq D] [Fintype Q] [DecidableEq Q]
    {M : Map D Q} {T₁ : M.SpTree} {k n : ℕ} {cd : D ≃ Fin (3 * k)} {vi : Q ≃ Fin n}
    {A V : ℕ → ℕ} {cn : Q → Q} {wP : Q → ℕ} {W : ℕ} {P : Input} {c : Config}
    {bV bPr bU bWC bD bS bD₂ bS₂ : ℕ}
    (hM : M.IsPlane) (hT3 : ∀ δ, M.IsTriangle δ) (hk2 : 2 ≤ k)
    (hAcd : ∀ x, A (cd x) = cd (M.α x)) (hφ : ∀ x, (cd (M.φ x) : ℕ) = phi3 (cd x))
    (hV : ∀ x, V (cd x) = vi (M.vert x))
    (hconc : ∀ u, Map.wcf cn (wR wP) u = (c.nmem (bWC + vi u) : ℝ) / ∑ v, (wP v : ℝ))
    (hpos : 0 < ∑ v, wP v)
    (hlay : 11 * k ≤ bV ∧ bV + 3 * k ≤ bPr ∧ bPr + n ≤ bU ∧
      bU + (Nat.log 2 n + 1) * n ≤ bWC ∧ bWC + n ≤ bD ∧ bD + n ≤ bS ∧ bS + n ≤ bD₂ ∧
      bD₂ + n ≤ bS₂ ∧ bS₂ + n ≤ W)
    (hWt : 11 * k + 3 * ∑ v, wP v + 4 ≤ W)
    (hc : WordsBounded W c) (hR : CRegs k c) (h140 : c.nreg 140 = 0) (h141 : c.nreg 141 = 1)
    (h147 : c.nreg 147 = 0) (h161 : c.nreg 161 = n) (h162 : c.nreg 162 = bV)
    (h215 : c.nreg 215 = bPr) (h250 : c.nreg 250 = bWC) (h252 : c.nreg 252 = bS)
    (h253 : c.nreg 253 = bD) (h254 : c.nreg 254 = bU) (h255 : c.nreg 255 = vi T₁.root)
    (h381 : c.nreg 381 = bD₂) (h382 : c.nreg 382 = bS₂)
    (mA : ∀ x < 3 * k, c.nmem x = A x) (mV : ∀ x < 3 * k, c.nmem (bV + x) = V x)
    (hPr : ∀ v (h : v ≠ T₁.root), c.nmem (bPr + vi v) = cd (T₁.par v h)) :
    ∃ c' t, Exec P W step8run c c' t ∧
      t ≤ (125 * Nat.log 2 n + 564) * k + (39 * n + 122) * Nat.log 2 n + 94 * n + 468 ∧
      (∀ a, 11 * k ≤ a → (a < bU ∨ bU + (Nat.log 2 n + 1) * n ≤ a) → (a < bD ∨ bS₂ + n ≤ a) →
        c'.nmem a = c.nmem a) ∧ (∀ x < 3 * k, c'.nmem x = A x) ∧
      ∃ δ : D, (cd δ : ℕ) = c'.nreg 353 ∧ ¬ T₁.IsTree δ ∧
        ∑ v ∈ T₁.inC δ, Map.wcf cn (wR wP) v ≤ 2 / 3 ∧
        ∑ v ∈ T₁.outC δ, Map.wcf cn (wR wP) v ≤ 2 / 3 := by
  set wv : Q → ℕ := fun u => c.nmem (bWC + vi u)
  have htot : ∑ v, wv v = ∑ v, wP v := by
    have hS : (0 : ℝ) < ∑ v, (wP v : ℝ) := by exact_mod_cast hpos
    have e := Map.sum_wcf cn (wR wP)
    have e1 : ∑ v, wR wP v = 1 := by unfold wR; rw [← sum_div, div_self hS.ne']
    simp only [hconc, ← sum_div] at e
    rw [e1, div_eq_one_iff_eq hS.ne'] at e
    exact_mod_cast e
  obtain ⟨c', t, e, ht, hfr, hlo, δ, hδ, hnt, h1, h2⟩ := step8run_tree (P := P) (c := c) (T := T₁) (cd := cd)
    (vi := vi) (A := A) (V := V) (w := fun u => c.nmem (bWC + u)) wv hM hT3 hk2 hAcd hφ hV
    (fun x => rfl) hlay (by rw [htot]; exact hWt) hc hR h140 h141 h147 h161 h162 h215 h250 h252
    h253 h254 h255 h381 h382 mA mV (fun u _ => rfl) hPr
  exact ⟨c', t, e, ht, hfr, hlo, δ, hδ, hnt, le_two_thirds_wcf hpos hconc h1,
    le_two_thirds_wcf hpos hconc h2⟩


end MillerProg

end PlanarSeparator
