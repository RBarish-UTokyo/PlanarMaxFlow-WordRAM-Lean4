module

public import PlanarFlow.NegSSSP.ChildCopy

/-!
# The child encodings on the machine, part 3: the frame of a child

**`ceProg_exec`**: from the frame of a piece `P` (`InP … n P d e`) and the sides of its darts
at `Ob` (`SD[h] = s` exactly on the darts of `Q`, `SideOK`), `ceProg = ceLoad ; ciProg ;
ccProg` writes the frame of the child `Q` with `n - 1` rounds at `Cb`
(`InP … (n - 1) Q Cb (Cb + fsz #Q (ck N Q))`): the canonical numbering of `Q` (`fL_child`), its
reversal (`cα_child`) and its first-return rotation (`walk_child`, the walk of the parent's
`cσ`), the global identifiers, tails, heads and lengths copied. Within
**`44 k + 41 m + 70`** steps (`m = #P`, `k = #(rcl N P)`; the walks sum to at most `k`,
`sum_walk_le`). Memory written only in the scratch `NI`, `OLD` (`k` words each) and the child's
data; registers `2930 … 2965` only.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace NegSSSP

namespace Frame

open Finset Orbit WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

/-- The sizes of the parent: `r2932 = m`, `r2933 = k` from its frame at `r2931 = d`. -/
def ceLoad : Stmt := block [.constN 2942 1, .addN 2942 2931 2942, .loadN 2932 2942,
  .constN 2942 2, .addN 2942 2931 2942, .loadN 2933 2942]

/-- **The frame of a child** (see the module docstring). -/
def ceProg : Stmt := .seq (.seq ceLoad ciProg) ccProg

theorem ceProg_natOnly : Klein.natOnly ceProg = true := by kernel_rfl

variable {I : Input} {W : ℕ}

theorem ceLoad_exec (c : Config) (hc : WordsBounded W c) {d : ℕ} (r31 : c.nreg 2931 = d)
    (w : d + 2 ≤ W) :
    ∃ c' t, Exec I W ceLoad c c' t ∧ t = 6 ∧ c'.nreg 2932 = c.nmem (d + 1) ∧
      c'.nreg 2933 = c.nmem (d + 2) ∧
      (∀ r, r ≠ 2932 → r ≠ 2933 → r ≠ 2942 → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold ceLoad
  exec_block
  all_goals try ((try config_simp); (try simp only [r31]); omega)
  refine ⟨rfl, ?_, ?_, fun r h1 h2 h3 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try (simp only [r31])
  all_goals try (simp only [upd_apply]; split_ifs <;> omega)

theorem iterate_congr_lt {F G : ℕ → ℕ} {k : ℕ} (hFG : ∀ x < k, F x = G x)
    (hG : ∀ x < k, G x < k) : ∀ i x, x < k → F^[i] x = G^[i] x ∧ G^[i] x < k := by
  intro i
  induction i with
  | zero => intro x hx; exact ⟨rfl, hx⟩
  | succ i ih =>
    intro x hx
    obtain ⟨h1, h2⟩ := ih x hx
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', h1, hFG _ h2]
    exact ⟨rfl, hG _ h2⟩

theorem sum_range_getD (L : List ℕ) (f : ℕ → ℕ) :
    ∑ j ∈ Finset.range L.length, f (L.getD j 0) = (L.map f).sum := by
  induction L with
  | nil => simp
  | cons x xs ih =>
    rw [List.length_cons, Finset.sum_range_succ', List.map_cons, List.sum_cons]
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    rw [ih]; omega

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {g : GIds D V} {N : CombMap D V F}

/-- The walks of the child. -/
noncomputable def ceT (g : GIds D V) (N : CombMap D V F) (P Q : Finset D) (Lc : List ℕ)
    (j : ℕ) : ℕ :=
  retIdx (ρP N P) (rcl N Q) (cδ g N P (Lc.getD j 0))

/-- **The child's frame from the cells written** (pure). -/
theorem inP_of_cells {ℓ : D → ℤ} {L n : ℕ} {P Q : Finset D} {s d e Cb : ℕ} {SD : ℕ → ℕ}
    {c : Config} (hin : InP g N ℓ L n P d e c) (hs : SideOK P Q s SD (cδ g N P))
    {mem₁ : ℕ → ℕ} (hM : ∀ a, d ≤ a → a < d + 4 + 6 * ck N P → mem₁ a = c.nmem a)
    (c' : Config) (h0 : c'.nmem Cb = c.nmem d - 1) (h1 : c'.nmem (Cb + 1) = Q.card)
    (h2 : c'.nmem (Cb + 2) = ck N Q) (h3 : c'.nmem (Cb + 3) = c.nmem (d + 3))
    (hCC : CCells Cb (ck N Q) (chL g N P s SD) (fun x => mem₁ (d + 4 + x))
      (fun x => mem₁ (d + 4 + ck N P + x)) (fun x => mem₁ (d + 4 + 2 * ck N P + x))
      (fun x => mem₁ (d + 4 + 3 * ck N P + x)) (fun x => mem₁ (d + 4 + 4 * ck N P + x))
      (ceT g N P Q (chL g N P s SD)) c'.nmem (ck N Q))
    (hLN : ∀ j (hj : j < Q.card) (hj' : j < (chL g N P s SD).length),
      c'.nmem (Cb + 4 + 5 * ck N Q + j) = mem₁ (d + 4 + 5 * ck N P + (chL g N P s SD)[j])) :
    InP g N ℓ L (n - 1) Q Cb (Cb + fsz Q.card (ck N Q)) c' := by
  have he := penc_canon (g := g) (N := N) P
  set k := ck N P with hk
  set Lc := chL g N P s SD with hLc
  have hLk : ∀ x ∈ Lc, x < k := fun x hx => chL_lt x hx
  have hLlen : Lc.length = ck N Q := length_chL hs
  have hSG : ∀ x < k, mem₁ (d + 4 + 2 * k + x) = cσ g N P x := fun x hx => by
    rw [hM _ (by omega) (by omega)]; exact hin.σ x hx
  have hIt := iterate_congr_lt (k := k) (F := fun x => mem₁ (d + 4 + 2 * k + x))
    (G := cσ g N P) hSG (fun x hx => he.σ_lt x hx)
  have hlen' := length_oldA hs
  have hQ := ck_ge (N := N) Q
  refine ⟨rfl, ?_, h1, h2, ?_, fun h hh => ?_, fun h hh => ?_, fun h hh => ?_, fun h hh => ?_,
    fun h hh => ?_, fun h hh => ?_⟩
  · rw [h0, hin.rn]
  · rw [h3, hin.rL]
  · have hj : h < Lc.length := by omega
    have hx := hLk _ (List.getElem_mem hj)
    have hc := (hCC h hh hj).1
    beta_reduce at hc
    rw [hc, hM _ (by omega) (by omega), hin.gd _ hx, cδ_child hs hj]
  · have hj : h < Lc.length := by omega
    have hx := hLk _ (List.getElem_mem hj)
    have hc := (hCC h hh hj).2.1
    beta_reduce at hc
    rw [hc, hM _ (by omega) (by omega), hin.α _ hx, cα_child hs hj]
  · have hj : h < Lc.length := by omega
    have hx := hLk _ (List.getElem_mem hj)
    obtain ⟨-, -, -, w4⟩ := walk_child hs hj
    have eT : ceT g N P Q Lc h = retIdx (ρP N P) (rcl N Q) (cδ g N P Lc[h]) := by
      simp only [ceT, List.getD_eq_getElem _ _ hj]
    have hc := (hCC h hh hj).2.2.1
    beta_reduce at hc
    rw [hc, eT, (hIt _ _ hx).1, w4]
  · have hj : h < Lc.length := by omega
    have hx := hLk _ (List.getElem_mem hj)
    have hc := (hCC h hh hj).2.2.2.1
    beta_reduce at hc
    rw [hc, hM _ (by omega) (by omega), hin.gt _ hx, cδ_child hs hj]
  · have hj : h < Lc.length := by omega
    have hx := hLk _ (List.getElem_mem hj)
    have hc := (hCC h hh hj).2.2.2.2
    beta_reduce at hc
    rw [hc, hM _ (by omega) (by omega), hin.gh _ hx, cδ_child hs hj]
  · have hj : h < Lc.length := by omega
    have hxm : Lc[h] < P.card := by
      have hp := apnd_prefix (oldA s P.card SD) ((oldA s P.card SD).map (cα g N P))
      have hjA : h < (oldA s P.card SD).length := by omega
      have := hp.getElem hjA
      simp only [hLc, chL] at this ⊢
      rw [← this]
      exact oldA_lt (List.getElem_mem hjA)
    have hmk := ck_ge (N := N) P
    rw [hLN h hh hj, hM _ (by omega) (by omega), hin.ln _ hxm, cδ_child hs hj]

set_option maxHeartbeats 4000000 in
/-- The sizes and the list of the child (`ceLoad ; ciProg`). -/
theorem ce1_exec {ℓ : D → ℤ} {L n : ℕ} {P Q : Finset D} {s d e : ℕ} (c : Config)
    (hc : WordsBounded W c) (hin : InP g N ℓ L n P d e c) {Ob Xb Yb : ℕ}
    (r30 : c.nreg 2930 = s) (r31 : c.nreg 2931 = d) (r34 : c.nreg 2934 = Ob)
    (r35 : c.nreg 2935 = Xb) (r36 : c.nreg 2936 = Yb)
    (hs : SideOK P Q s (fun x => c.nmem (Ob + x)) (cδ g N P))
    (wX : Xb + ck N P ≤ W) (wY : Yb + ck N P ≤ W) (lO : Ob + P.card ≤ W)
    (wd : d + 4 + 6 * ck N P ≤ W) (wk : ck N P + 4 ≤ W)
    (dXY : Xb + ck N P ≤ Yb ∨ Yb + ck N P ≤ Xb)
    (dXO : Xb + ck N P ≤ Ob ∨ Ob + P.card ≤ Xb) (dYO : Yb + ck N P ≤ Ob ∨ Ob + P.card ≤ Yb)
    (dXd : Xb + ck N P ≤ d ∨ d + 4 + 6 * ck N P ≤ Xb)
    (dYd : Yb + ck N P ≤ d ∨ d + 4 + 6 * ck N P ≤ Yb) :
    ∃ c₁ t₁, Exec I W (.seq ceLoad ciProg) c c₁ t₁ ∧
      t₁ ≤ 5 * ck N P + 15 * P.card + 17 * Q.card + 31 ∧
      c₁.nreg 2950 = Q.card ∧ c₁.nreg 2951 = ck N Q ∧
      LArr Xb Yb (ck N P) (chL g N P s (fun x => c.nmem (Ob + x))) c₁ ∧
      c₁.nreg 2939 = 1 ∧ c₁.nreg 2952 = d + 4 ∧
      c₁.nreg 2953 = d + 4 + ck N P ∧ c₁.nreg 2954 = d + 4 + 2 * ck N P ∧
      c₁.nreg 2955 = d + 4 + 3 * ck N P ∧ c₁.nreg 2956 = d + 4 + 4 * ck N P ∧
      c₁.nreg 2957 = d + 4 + 5 * ck N P ∧
      (∀ a, (a < Xb ∨ Xb + ck N P ≤ a) → (a < Yb ∨ Yb + ck N P ≤ a) → c₁.nmem a = c.nmem a) ∧
      (∀ r, (r < 2932 ∨ (2933 < r ∧ r < 2938) ∨ 2957 < r) → c₁.nreg r = c.nreg r) ∧
      c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
  have he := penc_canon (g := g) (N := N) P
  have hmk := ck_ge (N := N) P
  obtain ⟨c₀, t₀, e₀, ht₀, g32, g33, gn₀, gm₀, gr₀, grm₀, go₀⟩ :=
    ceLoad_exec (I := I) c hc r31 (by omega)
  rw [hin.rm] at g32
  rw [hin.rk] at g33
  have hAL : ∀ x < ck N P, c₀.nmem (d + 4 + ck N P + x) < ck N P := fun x hx => by
    rw [gm₀, hin.α x hx]; exact he.α_lt x hx
  obtain ⟨c₁, t₁, e₁, ht₁, h50, h51, hLA, s38, s39, s52, s53, s54, s55, s56, s57, hMO, hR1,
      hr₁, hrm₁, ho₁⟩ :=
    ciProg_exec (P := I) c₀ e₀.wb_right (s := s) (d := d) (m := P.card) (k := ck N P)
      (Ob := Ob) (Xb := Xb) (Yb := Yb)
      (by rw [gn₀ _ (by omega) (by omega) (by omega)]; exact r30)
      (by rw [gn₀ _ (by omega) (by omega) (by omega)]; exact r31) g32 g33
      (by rw [gn₀ _ (by omega) (by omega) (by omega)]; exact r34)
      (by rw [gn₀ _ (by omega) (by omega) (by omega)]; exact r35)
      (by rw [gn₀ _ (by omega) (by omega) (by omega)]; exact r36) hmk hAL wX
      wY lO (by omega) wk dXY dXO dYO (by omega) (by omega)
  have eSD : (fun x => c₀.nmem (Ob + x)) = fun x => c.nmem (Ob + x) := by rw [gm₀]
  have eL : ciL s P.card (fun x => c₀.nmem (Ob + x)) (fun x => c₀.nmem (d + 4 + ck N P + x)) =
      chL g N P s (fun x => c.nmem (Ob + x)) := by
    rw [eSD]
    unfold ciL chL
    congr 1
    apply List.map_congr_left
    intro x hx
    have := oldA_lt hx
    rw [gm₀, hin.α x (by omega)]
  have eA : (oldA s P.card fun x => c₀.nmem (Ob + x)).length = Q.card := by
    rw [eSD, length_oldA hs]
  rw [eL] at h51 hLA
  rw [eA] at h50 ht₁
  rw [length_chL hs] at h51
  refine ⟨c₁, t₀ + t₁, .seq e₀ e₁, by omega, h50, h51, hLA, s39, s52, s53, s54, s55, s56, s57,
    fun a h1 h2 => by rw [hMO a h1 h2, gm₀], fun r hr => ?_, by rw [hr₁, gr₀],
    by rw [hrm₁, grm₀], by rw [ho₁, go₀]⟩
  rw [hR1 r (by omega), gn₀ r (by omega) (by omega) (by omega)]

set_option maxHeartbeats 4000000 in
/-- **The frame of a child on the machine** (see the module docstring). -/
theorem ceProg_exec {ℓ : D → ℤ} {L n : ℕ} {P Q : Finset D} {s d e : ℕ} (c : Config)
    (hc : WordsBounded W c) (hin : InP g N ℓ L n P d e c) {Ob Xb Yb Cb : ℕ}
    (r30 : c.nreg 2930 = s) (r31 : c.nreg 2931 = d) (r34 : c.nreg 2934 = Ob)
    (r35 : c.nreg 2935 = Xb) (r36 : c.nreg 2936 = Yb) (r37 : c.nreg 2937 = Cb)
    (hs : SideOK P Q s (fun x => c.nmem (Ob + x)) (cδ g N P))
    (lX : Xb + ck N P ≤ Cb) (lY : Yb + ck N P ≤ Cb) (lO : Ob + P.card ≤ W)
    (ld : d + 4 + 6 * ck N P ≤ Cb) (wk : ck N P + 4 ≤ W)
    (dXY : Xb + ck N P ≤ Yb ∨ Yb + ck N P ≤ Xb)
    (dXO : Xb + ck N P ≤ Ob ∨ Ob + P.card ≤ Xb) (dYO : Yb + ck N P ≤ Ob ∨ Ob + P.card ≤ Yb)
    (dXd : Xb + ck N P ≤ d ∨ d + 4 + 6 * ck N P ≤ Xb)
    (dYd : Yb + ck N P ≤ d ∨ d + 4 + 6 * ck N P ≤ Yb)
    (wC : Cb + fsz Q.card (ck N Q) ≤ W) :
    ∃ c' t, Exec I W ceProg c c' t ∧ t ≤ 44 * ck N P + 41 * P.card + 70 ∧
      InP g N ℓ L (n - 1) Q Cb (Cb + fsz Q.card (ck N Q)) c' ∧
      (∀ a, (a < Cb ∨ Cb + fsz Q.card (ck N Q) ≤ a) → (a < Xb ∨ Xb + ck N P ≤ a) →
        (a < Yb ∨ Yb + ck N P ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, (r < 2930 ∨ 2965 < r) → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have he := penc_canon (g := g) (N := N) P
  have hmk := ck_ge (N := N) P
  have hQk : ck N Q ≤ ck N P := card_le_card (rcl_mono' hs.1)
  have hQm : Q.card ≤ P.card := card_le_card hs.1
  have hQ := ck_ge (N := N) Q
  unfold fsz at wC ⊢
  obtain ⟨c₁, t₁, e₁, ht₁, h50, h51, hLA, s39, s52, s53, s54, s55, s56, s57, M1, R1, hr₁, hrm₁,
      ho₁⟩ := ce1_exec (I := I) c hc hin r30 r31 r34 r35 r36 hs (by omega) (by omega) lO
      (by omega) wk dXY dXO dYO dXd dYd
  set Lc := chL g N P s (fun x => c.nmem (Ob + x)) with hLc
  have hLk : ∀ x ∈ Lc, x < ck N P := fun x hx => chL_lt x hx
  have hLlen : Lc.length = ck N Q := length_chL hs
  have hSG : ∀ x < ck N P, c₁.nmem (d + 4 + 2 * ck N P + x) = cσ g N P x := fun x hx => by
    rw [M1 _ (by omega) (by omega)]; exact hin.σ x hx
  have hIt := iterate_congr_lt (k := ck N P) (F := fun x => c₁.nmem (d + 4 + 2 * ck N P + x))
    (G := cσ g N P) hSG (fun x hx => he.σ_lt x hx)
  have hTw : ∀ j (hj : j < Lc.length), 1 ≤ ceT g N P Q Lc j ∧
      (fun x => c₁.nmem (d + 4 + 2 * ck N P + x))^[ceT g N P Q Lc j] Lc[j] ∈ Lc ∧
      ∀ i, 1 ≤ i → i < ceT g N P Q Lc j →
        (fun x => c₁.nmem (d + 4 + 2 * ck N P + x))^[i] Lc[j] ∉ Lc := fun j hj => by
    obtain ⟨w1, w2, w3, -⟩ := walk_child hs hj
    have hx := hLk _ (List.getElem_mem hj)
    have eT : ceT g N P Q Lc j = retIdx (ρP N P) (rcl N Q) (cδ g N P Lc[j]) := by
      simp only [ceT, List.getD_eq_getElem _ _ hj]
    refine ⟨by rw [eT]; exact w1, by rw [eT, (hIt _ _ hx).1]; exact w2,
      fun i h1 h2 => by rw [(hIt _ _ hx).1]; exact w3 i h1 (by rw [← eT]; exact h2)⟩
  have hAm : ∀ j (hj : j < Lc.length), c₁.nmem (d + 4 + ck N P + Lc[j]) ∈ Lc := fun j hj => by
    have hx := hLk _ (List.getElem_mem hj)
    rw [M1 _ (by omega) (by omega), hin.α _ hx]
    exact cα_mem_chL hs hj
  obtain ⟨c₂, t₂, e₂, ht₂, m0, m1, m2, m3, hCC, hLN, hM2, hR2, hr₂, hrm₂, ho₂⟩ :=
    ccProg_exec (P := I) c₁ e₁.wb_right (d := d) (Xb := Xb) (Yb := Yb) (Cb := Cb)
      (ms := Q.card) (ks := ck N Q) (k := ck N P) (Gb := d + 4) (Ab := d + 4 + ck N P)
      (Sb := d + 4 + 2 * ck N P) (Tb := d + 4 + 3 * ck N P) (Hb := d + 4 + 4 * ck N P)
      (Lb := d + 4 + 5 * ck N P) (L := Lc) (T := ceT g N P Q Lc)
      (by rw [R1 _ (by omega)]; exact r31) (by rw [R1 _ (by omega)]; exact r35)
      (by rw [R1 _ (by omega)]; exact r36) (by rw [R1 _ (by omega)]; exact r37) s39 h50 h51
      s52 s53 s54 s55 s56 s57 hLlen hQ hLk hLA
      (fun x hx => by rw [hSG x hx]; exact he.σ_lt x hx)
      (fun x hx => by rw [M1 _ (by omega) (by omega), hin.α x hx]; exact he.α_lt x hx)
      hAm hTw (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) lX lY
      (by omega) hQk (by omega)
  have hsum : ∑ j ∈ Finset.range (ck N Q), ceT g N P Q Lc j ≤ ck N P := by
    rw [← hLlen]
    have := sum_walk_le (g := g) (N := N) hs
    rw [← sum_range_getD Lc (fun x => retIdx (ρP N P) (rcl N Q) (cδ g N P x))] at this
    exact this
  have hInP := inP_of_cells (ℓ := ℓ) (L := L) hin hs (mem₁ := c₁.nmem)
    (fun a h1 h2 => M1 a (by omega) (by omega)) c₂ (by rw [m0, M1 _ (by omega) (by omega)])
    m1 m2 (by rw [m3, M1 _ (by omega) (by omega)]) hCC (fun j hj _ => hLN j hj)
  unfold fsz at hInP
  refine ⟨c₂, t₁ + t₂, .seq e₁ e₂, by omega, hInP, fun a h1 h2 h3 => ?_, fun r hr => ?_,
    by rw [hr₂, hr₁], by rw [hrm₂, hrm₁], by rw [ho₂, ho₁]⟩
  · rw [hM2 a (by omega), M1 a h2 h3]
  · rw [hR2 r (by omega), R1 r (by omega)]

end Frame

end NegSSSP

end PlanarFlow
