module

public import PlanarFlow.Monge.FRSettle

/-!
# FR-Dijkstra on the machine: the main loop

A round of the main loop compares the root of the heap of the vertices (a vertex `x` and its
key) with the root of the heap of the half blocks (a half block and its item): if the item is
smaller, or no vertex is present, the item is *popped* (`bPop`: its row is extracted, and its
target is settled unless it is settled already); otherwise `x` is settled (`settle`). The loop
runs while one of the roots is present (`gflag`).

* `mBody_exec`: one round keeps the state `MI` (the state of the run `MSt`, a run of
  Dijkstra's algorithm `MRun`), at the cost of the decrease of the potential `pot`: the costs
  `vc` of the unsettled vertices, `Cx` per row not extracted of every half block, and the
  potential `potN` of the activations.
* `mainLoop_exec`: at the end both heaps are empty, and the run is closed under the arcs
  (`MSt.cover`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace Monge

namespace FR

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs Heap

/-! ### The programs -/

/-- The flag of the main loop: the sum of the present flags of both roots. -/
def gflag : Stmt :=
  block [.addN 191 114 110, .loadN 191 191, .addN 191 109 191, .loadN 192 191,
    .addN 191 242 111, .loadN 191 191, .mulN 191 191 118, .addN 191 191 241, .loadN 193 191,
    .addN 190 192 193]

/-- **Pop the item of the half block of the leaf `r290`**: extract it, offer the next item,
and settle its target unless it is settled. -/
def bPop : Stmt :=
  .seq bload <|
  .seq (.seq ext bsync) <|
  .seq (block [.addN 180 122 254, .addN 192 107 180, .loadN 192 192, .copyR 180 250]) <|
  .ifLtN 192 110 settle .skip

/-- **One round**: the root `x` of the heap of the vertices (present flag `r192`, key `rr180`)
and the root `r290` of the heap of the half blocks (present flag `r193`, key `rr190`); pop the
item if it is smaller or no vertex is present, else settle `x`. -/
def mBody : Stmt :=
  .seq (block [.addN 191 114 110, .loadN 180 191, .addN 191 109 180, .loadN 192 191,
    .loadR 180 191, .addN 191 242 111, .loadN 290 191, .mulN 191 290 118, .addN 191 191 241,
    .loadN 193 191, .loadR 190 191]) <|
  .seq (.ifLtN 192 110 bPop (.ifLtN 193 110 settle (.ifLtR 190 180 bPop settle))) gflag

/-! ### The potential -/

/-- The cost of a round settling `y`. -/
def vc (P : Prm) (y : ℕ) : ℕ := settleCost P y + 40

/-- The cost of a round popping an item, per row. -/
def Cx (P : Prm) : ℕ := extCost P.Lv + LD P.Lv + 49 * P.TB + 100

/-- The costs of the unsettled vertices. -/
def potS (P : Prm) (nm : ℕ → ℕ) : ℕ :=
  ∑ y ∈ Finset.range P.N, if sfV P nm y = 0 then vc P y else 0

open Classical in
/-- The rows not extracted of the half blocks. -/
noncomputable def potX (P : Prm) (X : ℕ → ℕ → ℕ → Prop) : ℕ :=
  bSum P fun t k => ((Finset.range (hbNr P.b (2 ^ t) k)).filter fun ρ => ¬ X t k ρ).card

/-- **The potential of the main loop.** -/
noncomputable def pot (P : Prm) (X : ℕ → ℕ → ℕ → Prop) (nm : ℕ → ℕ) : ℕ :=
  potS P nm + Cx P * potX P X + potN P nm

variable {P : Prm} {I : Input}

/-- Settling `x` lowers the costs of the unsettled vertices by its cost. -/
lemma potS_step {K : ℕ} {v : ℕ → ℕ} {d : ℕ → ℤ} {nm nm' : ℕ → ℕ} {rm rm' : ℕ → ℝ} {x : ℕ}
    {dK : ℤ} (hG1 : Gh P K v d nm rm)
    (hG2 : Gh P (K + 1) (Function.update v K x) (Function.update d K dK) nm' rm')
    (hs1 : ∀ y < P.N, sfV P nm y ≤ 1) (hs2 : ∀ y < P.N, sfV P nm' y ≤ 1) (hx : x < P.N)
    (hxs : sfV P nm x = 0) (hnv : ∀ j < K, v j ≠ x) : potS P nm' + vc P x = potS P nm := by
  have key : ∀ y < P.N, (sfV P nm' y = 0 ↔ sfV P nm y = 0 ∧ y ≠ x) := by
    intro y hy
    have e : sfV P nm' y = 1 ↔ sfV P nm y = 1 ∨ y = x := by
      rw [hG2.sf y hy, hG1.sf y hy]
      constructor
      · rintro ⟨i, hi, e⟩
        rcases Nat.lt_or_ge i K with h | h
        · rw [Function.update_of_ne (by omega)] at e; exact Or.inl ⟨i, h, e⟩
        · rw [show i = K by omega, Function.update_self] at e; exact Or.inr e.symm
      · rintro (⟨i, hi, e⟩ | rfl)
        · exact ⟨i, by omega, by rw [Function.update_of_ne (by omega)]; exact e⟩
        · exact ⟨K, by omega, Function.update_self ..⟩
    have := hs1 y hy; have := hs2 y hy
    constructor
    · intro h; refine ⟨by by_contra h'; have := e.2 (Or.inl (by omega)); omega, fun h' => ?_⟩
      have := e.2 (Or.inr h'); omega
    · rintro ⟨h1, h2⟩; by_contra h'; rcases e.1 (by omega) with h3 | h3 <;> omega
  unfold potS
  have hm : x ∈ Finset.range P.N := Finset.mem_range.2 hx
  rw [← Finset.add_sum_erase _ _ hm, ← Finset.add_sum_erase _ _ hm]
  have hsum : ∑ y ∈ (Finset.range P.N).erase x, (if sfV P nm' y = 0 then vc P y else 0) =
      ∑ y ∈ (Finset.range P.N).erase x, (if sfV P nm y = 0 then vc P y else 0) := by
    refine Finset.sum_congr rfl fun y hy => ?_
    have hy' := Finset.mem_erase.1 hy
    have := key y (Finset.mem_range.1 hy'.2)
    split_ifs <;> first | rfl | tauto
  have h1 : (if sfV P nm' x = 0 then vc P x else 0) = 0 := by
    split_ifs with h
    · exact absurd rfl ((key x hx).1 h).2
    · rfl
  have h2 : (if sfV P nm x = 0 then vc P x else 0) = vc P x := by simp only [hxs, ↓reduceIte]
  rw [h1, h2, hsum]; ring

/-- The costs of the unsettled vertices depend only on the settled flags. -/
lemma potS_congr {nm nm' : ℕ → ℕ} (h : ∀ y < P.N, sfV P nm' y = sfV P nm y) :
    potS P nm' = potS P nm := by
  unfold potS
  exact Finset.sum_congr rfl fun y hy => by rw [h y (Finset.mem_range.1 hy)]

open Classical in
/-- **Extracting a row** lowers the rows not extracted by one. -/
lemma potX_step {X : ℕ → ℕ → ℕ → Prop} {t₀ k₀ m : ℕ} (ht : 2 ^ t₀ < P.b)
    (hk : k₀ * 2 ^ t₀ < P.b) (hm : m < hbNr P.b (2 ^ t₀) k₀) (hX : ¬ X t₀ k₀ m) :
    potX P (fun t k ρ => X t k ρ ∨ (t = t₀ ∧ k = k₀ ∧ ρ = m)) + 1 = potX P X := by
  have hs := bSum_step (P := P) (f := fun t k =>
      ((Finset.range (hbNr P.b (2 ^ t) k)).filter fun ρ => ¬ X t k ρ).card)
    (f' := fun t k => ((Finset.range (hbNr P.b (2 ^ t) k)).filter
      fun ρ => ¬ (X t k ρ ∨ (t = t₀ ∧ k = k₀ ∧ ρ = m))).card) ht hk fun t k _ _ hb => by
    congr 1
    ext ρ
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, fun h => h2 (Or.inl h)⟩
    · rintro ⟨h1, h2⟩
      refine ⟨h1, fun h => h.elim h2 fun ⟨e1, e2, _⟩ => hb ⟨e1, e2⟩⟩
  have hc : ((Finset.range (hbNr P.b (2 ^ t₀) k₀)).filter
      fun ρ => ¬ (X t₀ k₀ ρ ∨ (t₀ = t₀ ∧ k₀ = k₀ ∧ ρ = m))).card + 1 =
      ((Finset.range (hbNr P.b (2 ^ t₀) k₀)).filter fun ρ => ¬ X t₀ k₀ ρ).card := by
    have e : (Finset.range (hbNr P.b (2 ^ t₀) k₀)).filter
        (fun ρ => ¬ (X t₀ k₀ ρ ∨ (t₀ = t₀ ∧ k₀ = k₀ ∧ ρ = m))) =
        ((Finset.range (hbNr P.b (2 ^ t₀) k₀)).filter fun ρ => ¬ X t₀ k₀ ρ).erase m := by
      ext ρ
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_erase, true_and]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨fun h => h2 (Or.inr h), h1, fun h => h2 (Or.inl h)⟩
      · rintro ⟨h1, h2, h3⟩
        exact ⟨h2, fun h => h.elim h3 fun h' => h1 h'⟩
    rw [e, Finset.card_erase_add_one]
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨hm, hX⟩
  have key := (by omega : bSum P (fun t k => ((Finset.range (hbNr P.b (2 ^ t) k)).filter
      fun ρ => ¬ (X t k ρ ∨ (t = t₀ ∧ k = k₀ ∧ ρ = m))).card) + 1 =
    bSum P fun t k => ((Finset.range (hbNr P.b (2 ^ t) k)).filter fun ρ => ¬ X t k ρ).card)
  unfold potX
  convert key using 3
  funext t k
  congr 1
  ext ρ
  simp only [Finset.mem_filter]

/-- The rows not extracted, at most `2 b Lv`. -/
lemma potX_le {X : ℕ → ℕ → ℕ → Prop} : potX P X ≤ 2 * P.b * P.Lv := by
  classical
  unfold potX
  refine (bSum_le (g := fun _ => 1) fun t k _ _ => ?_).trans ?_
  · refine (Finset.card_filter_le _ _).trans ?_
    rw [Finset.card_range, Nat.one_mul]; exact Nat.min_le_left _ _
  · simp

/-! ### The flag -/

/-- **The flag of the main loop**: the present flags of both roots. -/
theorem gflag_exec (hL : Lay P) (c : Config) (hc : WordsBounded P.W c) (hG : Glob P c)
    (hX : GX P c) (hW : WinOK P.N (prV P c.nmem) (keyV P c.rmem) (wnV P c.nmem) 0)
    (hpr : ∀ y < P.N, prV P c.nmem y ≤ 1) (hB : BH P c.nmem c.rmem) :
    ∃ c' k', Exec I P.W gflag c c' k' ∧ k' ≤ 10 ∧
      c'.nreg 190 = prV P c.nmem (wnV P c.nmem 1) +
        tPr P.bh c.nmem (tWn P.bh (2 ^ P.TB) c.nmem 1) ∧
      (∀ r, r ≠ 190 → r ≠ 191 → r ≠ 192 → r ≠ 193 → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.nmem = c.nmem ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hw := lay_w hL
  have hbw := bh_le_W hL
  have h1 := (hW.under 1 le_rfl (by omega)).1
  have h2 := (win_root hB.win Nat.one_le_two_pow).1
  have hp1 := hB.pr _ h2
  have hpr1 := hpr _ h1
  have h2' : c.nmem (P.bh + 8 * 2 ^ P.TB + 2) < 2 ^ P.TB := by
    have := h2; unfold tWn at this; simpa using this
  have hp1' : c.nmem (P.bh + 8 * c.nmem (P.bh + 8 * 2 ^ P.TB + 2)) ≤ 1 := by
    have := hp1; unfold tPr tWn at this; simpa using this
  unfold gflag
  exec_block
  · rw [hG.r114, hG.r110]; omega
  · config_simp; rw [hG.r109, hG.r114, hG.r110]
    unfold wnV at h1; omega
  · config_simp; rw [hX.r242, hG.r111]; omega
  · config_simp; rw [hX.r242, hG.r111, hG.r118]; unfold tWn at h2; omega
  · config_simp; rw [hX.r242, hG.r111, hG.r118, hX.r241]; unfold tWn at h2; omega
  · config_simp; rw [hG.r109, hG.r114, hG.r110, hX.r242, hG.r111, hG.r118, hX.r241]
    unfold prV wnV at hpr1
    have hB' : c.nmem (c.nmem (P.bh + 8 * 2 ^ P.TB + 2) * 8 + P.bh) ≤ 1 := by
      rw [Nat.mul_comm, Nat.add_comm]; exact hp1'
    omega
  refine ⟨by omega, ?_, fun r h1 h2 h3 h4 => by config_simp; upd_tac, rfl, rfl, rfl, rfl⟩
  config_simp; rw [hG.r109, hG.r114, hG.r110, hX.r242, hG.r111, hG.r118, hX.r241]
  unfold prV wnV tPr tWn; rw [Nat.add_assoc]; ring_nf

/-! ### Settling the root of the heap of the vertices -/

/-- The state after a round. -/
structure Post (P : Prm) (c₀ : Config) (K : ℕ) (v : ℕ → ℕ) (d : ℕ → ℤ) (κ : ℝ)
    (X : ℕ → ℕ → ℕ → Prop) (c : Config) : Prop where
  wb : WordsBounded P.W c
  glob : Glob P c
  gx : GX P c
  data : Data P c
  keepN : ∀ r < 100, c.nreg r = c₀.nreg r
  keepR : ∀ r < 100, c.rreg r = c₀.rreg r
  out : c.output = c₀.output
  ms : MSt P K v d κ F2 F1 F2 X c.nmem c.rmem
  run : MRun P K v d
  pos : 0 < K

/-- **Settling the root `x` of the heap of the vertices** (`r180`, its key in `rr180`), not
larger than every present leaf of the heap of the half blocks. -/
theorem vPop_exec (hL : Lay P) (hDc : Crossing P.b P.D) (hF : Feas P) {K : ℕ} {v : ℕ → ℕ}
    {d : ℕ → ℤ} {κ : ℝ} {X : ℕ → ℕ → ℕ → Prop} (c : Config) (hc : WordsBounded P.W c)
    (hG : Glob P c) (hX : GX P c) (hDa : Data P c) (hS : MSt P K v d κ F2 F1 F2 X c.nmem c.rmem)
    (hR : MRun P K v d) (h180 : c.nreg 180 = wnV P c.nmem 1)
    (hpx : prV P c.nmem (wnV P c.nmem 1) = 1) (hk180 : c.rreg 180 = keyV P c.rmem (wnV P c.nmem 1))
    (hb : ∀ w < 2 ^ P.TB, tPr P.bh c.nmem w = 1 → keyV P c.rmem (wnV P c.nmem 1) ≤
      tKey P.bh c.rmem w) :
    ∃ c' k', Exec I P.W settle c c' k' ∧
      ∃ dK : ℤ, Post P c (K + 1) (Function.update v K (wnV P c.nmem 1))
        (Function.update d K dK) (keyV P c.rmem (wnV P c.nmem 1)) X c' ∧
        pot P X c'.nmem + k' + 40 ≤ pot P X c.nmem := by
  have hw := lay_w hL
  have hW := hS.hp.win
  have hx := (hW.under 1 le_rfl (by omega)).1
  have hmin := (win_root hW (by omega)).2
  generalize hxv : wnV P c.nmem 1 = x at hx hpx hmin h180 hk180 hb ⊢
  have hsx : sfV P c.nmem x = 0 := hS.hp.pr_sf x hx hpx
  have hnv : ∀ j < K, v j ≠ x := fun j hj e => by
    have := (hS.gh.sf x hx).2 ⟨j, hj, e⟩; omega
  -- the raised state
  have hS' := hS.raise (hS.kmin x hx hpx) (fun z hz hpz => (hmin z hz hpz).2) hb
  have hleast := hS.least hL (κ' := keyV P c.rmem x) (fun z hz hpz => (hmin z hz hpz).2) hb
  -- the key of `x` is justified
  obtain ⟨dK, hdK, hroot, hpar⟩ : ∃ dK : ℤ, keyV P c.rmem x = ((dK - P.p x : ℤ) : ℝ) ∧
      (K = 0 → x = P.r ∧ dK = 0) ∧
      (0 < K → ∃ i < K, ∃ ℓ, IsArc P (v i) x ℓ ∧ dK = d i + ℓ) := by
    rcases hS.gh.just x hx hpx with ⟨rfl, hk⟩ | ⟨i, hi, ℓ, ha, hk⟩
    · refine ⟨0, by rw [hk]; push_cast; ring, fun _ => ⟨rfl, rfl⟩, fun hK => ?_⟩
      exact absurd (hR.root hK) (hnv 0 hK)
    · exact ⟨d i + ℓ, by rw [hk], fun hK => by omega, fun _ => ⟨i, hi, ℓ, ha, rfl⟩⟩
  have hR' := hR.ext hnv hroot hpar fun i hi y ℓ ha hy => by
    have := hleast i hi y ℓ ha hy
    rw [hdK] at this; exact_mod_cast this
  obtain ⟨c', k', e, hk', hS₂, hG₂, hX₂, hDa₂, hK₂, hR₂, hO₂⟩ :=
    settle_exec (I := I) (dK := dK) hL hDc hF c hc hG hX hDa hS' (by rw [h180]; exact hx)
      (by rw [h180]; exact hsx) (fun _ h => h.elim) hk180 (by rw [h180]; exact hdK)
  rw [h180] at hk' hS₂
  refine ⟨c', k', e, dK, ⟨e.wb_right, hG₂, hX₂, hDa₂, hK₂, hR₂, hO₂, hS₂, hR', by omega⟩, ?_⟩
  have hpot := potS_step hS.gh hS₂.gh hS.hp.sf_le hS₂.hp.sf_le hx hsx hnv
  unfold pot vc at *
  omega

/-! ### Popping the item of a half block -/

/-- A present leaf of the heap of the half blocks needs a settled vertex. -/
lemma MSt.leaf_pos {K : ℕ} {v : ℕ → ℕ} {d : ℕ → ℤ} {κ : ℝ} {X : ℕ → ℕ → ℕ → Prop}
    {nm : ℕ → ℕ} {rm : ℕ → ℝ} (hL : Lay P) (hS : MSt P K v d κ F2 F1 F2 X nm rm) {w : ℕ}
    (hw : w < 2 ^ P.TB) (hpw : tPr P.bh nm w = 1) : 0 < K := by
  obtain ⟨t, k, ht, hk, rfl⟩ := hS.bh.leaf w hw hpw
  have hB := hS.blk t k ht hk
  have hr : tPr (tbQ P t k) nm (tWn (tbQ P t k) (2 ^ t) nm 1) = 1 := by
    have := hB.sync; rw [hpw] at this; split_ifs at this with h
    exact h
  obtain ⟨own, h0 | ⟨-, hT, -⟩⟩ := hB.rep
  · exact absurd hr (h0.2.2.2.no_start (win_root h0.2.2.2.win Nat.one_le_two_pow).1)
  have hnr : 0 < hbNr P.b (2 ^ t) k := by
    unfold hbNr; have := Nat.one_le_two_pow (n := t); omega
  obtain ⟨h1, h2, -⟩ := hT.heap.ok.act 0 hnr
  have : sib k * 2 ^ t + own 0 < P.N := by unfold hbNc at h1; have := hL.bN; omega
  obtain ⟨i, hi, -⟩ := (hS.gh.sf _ this).1 h2
  omega

lemma extCost_mono {t t' : ℕ} (h : t ≤ t') : extCost t ≤ extCost t' := by
  unfold extCost rmqCost; omega

lemma LD_mono {t t' : ℕ} (h : t ≤ t') : LD t ≤ LD t' := by unfold LD; omega

/-- **Popping the item of the half block of the root `r290` of the heap of the half blocks**,
not larger than every present vertex: its row is extracted, and its target is settled unless it
is settled already. -/
theorem bPop_exec (hL : Lay P) (hDc : Crossing P.b P.D) (hF : Feas P) {K : ℕ} {v : ℕ → ℕ}
    {d : ℕ → ℤ} {κ : ℝ} {X : ℕ → ℕ → ℕ → Prop} (c : Config) (hc : WordsBounded P.W c)
    (hG : Glob P c) (hX : GX P c) (hDa : Data P c) (hS : MSt P K v d κ F2 F1 F2 X c.nmem c.rmem)
    (hR : MRun P K v d) (h290 : c.nreg 290 = tWn P.bh (2 ^ P.TB) c.nmem 1)
    (hpw : tPr P.bh c.nmem (tWn P.bh (2 ^ P.TB) c.nmem 1) = 1)
    (hv : ∀ y < P.N, prV P c.nmem y = 1 →
      tKey P.bh c.rmem (tWn P.bh (2 ^ P.TB) c.nmem 1) ≤ keyV P c.rmem y) :
    ∃ c' k', Exec I P.W bPop c c' k' ∧ ∃ K' v' d' X', Post P c K' v' d'
        (tKey P.bh c.rmem (tWn P.bh (2 ^ P.TB) c.nmem 1)) X' c' ∧
      pot P X' c'.nmem + k' + 30 ≤ pot P X c.nmem := by
  have hw := lay_w hL
  have hbw := bh_le_W hL
  have := hL.m1; have := hL.m2; have := hL.m3; have := hL.m4; have := hL.m5; have := hL.m6
  have htb := tb_ge P
  obtain ⟨hwl, hmin⟩ := win_root hS.bh.win Nat.one_le_two_pow
  generalize hwv : tWn P.bh (2 ^ P.TB) c.nmem 1 = w at hwl hmin h290 hpw hv ⊢
  have hK0 := hS.leaf_pos hL hwl hpw
  obtain ⟨t, k, ht, hk, rfl⟩ := hS.bh.leaf w hwl hpw
  generalize hκ' : tKey P.bh c.rmem (bid P t k) = κ' at hv ⊢
  have hs1 : 1 ≤ 2 ^ t := Nat.one_le_two_pow
  have hb : ∀ w' < 2 ^ P.TB, tPr P.bh c.nmem w' = 1 → κ' ≤ tKey P.bh c.rmem w' :=
    fun w' h1 h2 => hκ' ▸ (hmin w' h1 h2).2
  have hB := hS.blk t k ht hk
  have hroot : tPr (tbQ P t k) c.nmem (tWn (tbQ P t k) (2 ^ t) c.nmem 1) = 1 := by
    have := hB.sync; rw [hpw] at this; split_ifs at this with h
    exact h
  have hkey0 := hB.key hroot
  rw [hκ'] at hkey0
  -- the popped key is at least the old one
  have hκκ : κ ≤ κ' := by
    obtain ⟨own, h0 | ⟨-, hT, hκo⟩⟩ := hB.rep
    · exact absurd hroot (h0.2.2.2.no_start (win_root h0.2.2.2.win hs1).1)
    obtain ⟨-, -, hXm, hmr, hown, hkey, -⟩ := hT.item hs1 (win_root hT.mem.win hs1).1 hroot
    rw [hkey0, hkey, ← hown]; exact hκo _ hmr hXm
  have hS' := hS.raise hκκ hv hb
  have hleast := hS.least hL hv hb
  -- the context of the half block
  refine spec_seq ?_
  refine spec_use (bload_exec (I := I) hL c hc hG hX ht hk h290 hB.leaf) ?_
  intro c₁ k₁ hk₁ hw₁ ⟨hH₁, hT₁, h182, h183, h284, h285, h181, hK₁, hR₁, hN₁, hM₁, hO₁⟩
  have k1 : ∀ r, (r < 120 ∨ (126 ≤ r ∧ r < 181) ∨ (184 ≤ r ∧ r < 189) ∨ (197 ≤ r ∧ r < 208) ∨
      (210 ≤ r ∧ r < 284) ∨ 286 ≤ r) → c₁.nreg r = c.nreg r := fun r hr => hK₁ r (by omega)
  have hG₁ : Glob P c₁ := hG.of fun r h1 h2 => k1 r (by omega)
  have hX₁ : GX P c₁ := hX.of fun r h1 h2 => k1 r (by omega)
  have hDa₁ : Data P c₁ := hDa.of hL (fun a _ => by rw [hN₁]) (fun a _ => by rw [hM₁])
  rw [← hN₁, ← hM₁] at hS'
  rw [← hN₁] at hroot
  rw [← hN₁, ← hM₁] at hkey0
  have hB' := hS'.blk t k ht hk
  obtain ⟨own, h0 | ⟨hf, hT, hκo⟩⟩ := hB'.rep
  · exact absurd hroot (h0.2.2.2.no_start (win_root h0.2.2.2.win hs1).1)
  have hrw := (win_root hT.mem.win hs1).1
  obtain ⟨-, -, hXm, hmr, hown, hkey, -⟩ := hT.item hs1 hrw hroot
  have hnc : 0 < hbNc P.b (2 ^ t) k := lt_of_le_of_lt (Nat.zero_le _)
    (hT.heap.ok.lt _ (hT.heap.ok.act _ hmr))
  -- the extraction
  refine spec_seq ?_
  obtain ⟨c₂, k₂, e₂, hk₂, hnst₂, h254, h250, hT₂, hf₂, hp₂, hkey₂, hW₂, hWl₂, hn₂, hr₂, hF₂⟩ :=
    extStep_exec hL (I := I) (κ := κ') (κ' := κ') ht hk c₁ hw₁ ⟨hG₁, hH₁, hDa₁⟩ hT₁ hX₁ h285
      h183 (hB'.ready hnc) hT (fun σ _ => rfl) hrw hroot le_rfl (le_of_eq hkey0.symm)
      hS'.bh.pr hS'.bh.win hS'.bh.wl
  refine ⟨c₂, k₂, e₂, ?_⟩
  have hw₂ := e₂.wb_right
  generalize hm : tMin (tbQ P t k) c₁.nmem (tWn (tbQ P t k) (2 ^ t) c₁.nmem 1) = m at *
  have hS₂ := hS'.extract hL ht hk hmr hT₂ hκo (by rw [hf₂]; exact hf) hp₂ hkey₂ hW₂ hWl₂
    (fun a h1 h2 => hn₂ a (by omega) h2) hr₂
  have k2 : ∀ r, ¬ (ExN r ∨ BSn r) → c₂.nreg r = c₁.nreg r := hF₂.n
  have hG₂ : Glob P c₂ := hG₁.of fun r h1 h2 => k2 r (by simp only [ExN, BSn, TPn]; omega)
  have hX₂ : GX P c₂ := hX₁.of fun r h1 h2 => k2 r (by simp only [ExN, BSn, TPn]; omega)
  have hQb := tbQ_le_bh ht hk
  have hQt : P.tb ≤ tbQ P t k := tb_le_tbQ
  have hlo2 : ∀ a < P.hb, c₂.nmem a = c₁.nmem a := fun a ha =>
    hn₂ a (Or.inl (by unfold Prm.hb at ha; omega)) (Or.inl (by unfold Prm.hb at ha; omega))
  have hlo2r : ∀ a < P.hb, c₂.rmem a = c₁.rmem a := fun a ha =>
    hr₂ a (Or.inl (by unfold Prm.hb at ha; omega)) (by unfold Prm.hb at ha; omega)
  have hhb : P.hb = P.wb + 3 * P.N := rfl
  have hDa₂ : Data P c₂ := hDa₁.of hL (fun a _ => hlo2 a (by omega)) (fun a _ => hlo2r a (by omega))
  have h122 : c₂.nreg 122 = k * 2 ^ t := by
    rw [k2 122 (by simp only [ExN, BSn, TPn]; omega)]; exact hH₁.r122
  have hy : k * 2 ^ t + m < P.b := by unfold hbNr at hmr; omega
  -- the potential so far
  have hpotS : potS P c₂.nmem = potS P c.nmem := by
    rw [← hN₁]; exact potS_congr fun y hy => hlo2 _ (by omega)
  have hpotN := potN_step (nm := c₁.nmem) (nm' := c₂.nmem) ht hk fun a h1 h2 =>
    hn₂ a (by omega) (Or.inl h2)
  have hN1p : potN P c₁.nmem = potN P c.nmem := by rw [hN₁]
  have hLDn : LD t * nst (tbQ P t k) (2 ^ t) c₂.nmem ≤
      LD t * nst (tbQ P t k) (2 ^ t) c₁.nmem + LD t := by
    have := Nat.mul_le_mul_left (LD t) hnst₂; rw [Nat.mul_add, Nat.mul_one] at this; exact this
  have hpotX := potX_step ht hk hmr hXm
  have hCx : Cx P * potX P X = Cx P * potX P (fun t' k' ρ => X t' k' ρ ∨
      (t' = t ∧ k' = k ∧ ρ = m)) + Cx P := by rw [← hpotX, Nat.mul_add, Nat.mul_one]
  have hcx : extCost t + LD t + 49 * P.TB + 100 ≤ Cx P := by
    have := lt_Lv' ht
    unfold Cx; have := extCost_mono (show t ≤ P.Lv by omega)
    have := LD_mono (show t ≤ P.Lv by omega); omega
  -- the target of the item
  refine spec_seq ?_
  exec_block
  · rw [h122, h254]; omega
  · config_simp; rw [hG₂.r107, h122, h254]; omega
  generalize hc₃ : (Config.mk _ _ _ _ _ _ : Config) = c₃
  have hw₃ : WordsBounded P.W c₃ := hc₃ ▸ ‹_›
  have f180 : c₃.nreg 180 = k * 2 ^ t + m := by rw [← hc₃]; config_simp; rw [h122, h254]
  have f192 : c₃.nreg 192 = sfV P c₂.nmem (k * 2 ^ t + m) := by
    rw [← hc₃]; config_simp; rw [hG₂.r107, h122, h254]; rfl
  have r180 : c₃.rreg 180 = κ' := by rw [← hc₃]; config_simp; rw [h250, ← hkey0]
  have fK : ∀ r, r ≠ 180 → r ≠ 192 → c₃.nreg r = c₂.nreg r := fun r h1 h2 => by
    rw [← hc₃]; config_simp; upd_tac
  have fR : ∀ r, r ≠ 180 → c₃.rreg r = c₂.rreg r := fun r h1 => by
    rw [← hc₃]; config_simp; upd_tac
  have e3N : c₃.nmem = c₂.nmem := by rw [← hc₃]
  have e3M : c₃.rmem = c₂.rmem := by rw [← hc₃]
  have e3O : c₃.output = c₂.output := by rw [← hc₃]
  have hG₃ : Glob P c₃ := hG₂.of fun r h1 h2 => fK r (by omega) (by omega)
  have hX₃ : GX P c₃ := hX₂.of fun r h1 h2 => fK r (by omega) (by omega)
  have hDa₃ : Data P c₃ := hDa₂.of hL (fun a _ => by rw [e3N]) (fun a _ => by rw [e3M])
  rw [← e3N, ← e3M] at hS₂
  have kN : ∀ r < 100, c₃.nreg r = c.nreg r := fun r hr => by
    rw [fK r (by omega) (by omega), k2 r (by simp only [ExN, BSn, TPn]; omega)]
    exact k1 r (by omega)
  have kR : ∀ r < 100, c₃.rreg r = c.rreg r := fun r hr => by
    rw [fR r (by omega), hF₂.r r (by simp only [ExR, TPr]; omega), hR₁]
  have kO : c₃.output = c.output := by rw [e3O, hF₂.o, hO₁]
  have hsf2 : sfV P c₂.nmem (k * 2 ^ t + m) ≤ 1 := by
    rw [← e3N]; exact hS₂.hp.sf_le _ (by have := hL.bN; omega)
  by_cases hys : sfV P c₂.nmem (k * 2 ^ t + m) = 0
  · -- settle the target
    refine spec_ifLtN_true (by rw [f192, hys, hG₃.r110]; omega) ?_
    -- its distance, through the owner of its row
    have hact := hT.heap.ok.act _ hmr
    obtain ⟨ha1, ha2, -⟩ := hact
    have hu : sib k * 2 ^ t + own m < P.N := by unfold hbNc at ha1; have := hL.bN; omega
    obtain ⟨i, hi, hvi⟩ := (hS'.gh.sf _ hu).1 ha2
    have hdi := hS'.gh.dist i hi
    have hne : sib k * 2 ^ t + own m ≠ k * 2 ^ t + m :=
      src_ne_tgt (lt_of_lt_of_le ha1 hbNc_le) (lt_of_lt_of_le hmr (Nat.min_le_left _ _))
    have hval : κ' = ((d i + P.D (v i) (k * 2 ^ t + m) - P.p (k * 2 ^ t + m) : ℤ) : ℝ) := by
      rw [hkey0, hkey, ← hown]
      unfold hbe; rw [hbF_live hy, ← hvi, hdi]; push_cast; ring
    have hys' : sfV P c.nmem (k * 2 ^ t + m) = 0 := by
      unfold sfV at hys ⊢; rw [← hN₁, ← hlo2 _ (by have := hL.bN; omega)]; exact hys
    have hnv : ∀ j < K, v j ≠ k * 2 ^ t + m := fun j hj e => by
      have := (hS.gh.sf _ (by have := hL.bN; omega)).2 ⟨j, hj, e⟩; omega
    have hR' := hR.ext (dK := d i + P.D (v i) (k * 2 ^ t + m)) hnv (fun h => by omega)
      (fun _ => ⟨i, hi, _, Or.inl ⟨by rw [hvi]; unfold hbNc at ha1; omega, hy,
        by rw [hvi]; exact hne, rfl⟩, rfl⟩)
      (fun i' hi' y ℓ ha hy' => by
        have := hleast i' hi' y ℓ ha hy'
        rw [hval] at this; exact_mod_cast this)
    obtain ⟨c₄, k₄, e₄, hk₄, hS₄, hG₄, hX₄, hDa₄, hK₄, hR₄, hO₄⟩ :=
      settle_exec (I := I) (dK := d i + P.D (v i) (k * 2 ^ t + m)) hL hDc hF c₃ hw₃ hG₃ hX₃
        hDa₃ hS₂ (by rw [f180]; have := hL.bN; omega) (by rw [f180, e3N]; exact hys)
        (fun y h => h.trans f180.symm) r180 (by rw [f180, hval])
    rw [f180] at hk₄ hS₄
    refine ⟨c₄, k₄, e₄, K + 1, Function.update v K (k * 2 ^ t + m),
      Function.update d K (d i + P.D (v i) (k * 2 ^ t + m)), _, ⟨e₄.wb_right, hG₄, hX₄, hDa₄,
      fun r hr => by rw [hK₄ r hr, kN r hr], fun r hr => by rw [hR₄ r hr, kR r hr],
      by rw [hO₄, kO], hS₄, hR', by omega⟩, ?_⟩
    have hpS := potS_step hS.gh hS₄.gh hS.hp.sf_le hS₄.hp.sf_le
      (by have := hL.bN; omega) hys' hnv
    have e3 : potS P c₃.nmem = potS P c.nmem := by rw [e3N, hpotS]
    have e3' : potN P c₃.nmem = potN P c₂.nmem := by rw [e3N]
    have e3 : potS P c₃.nmem = potS P c.nmem := by rw [e3N, hpotS]
    have e3' : potN P c₃.nmem = potN P c₂.nmem := by rw [e3N]
    unfold pot
    unfold vc at hpS
    generalize LD t * nst (tbQ P t k) (2 ^ t) c₂.nmem = A at *
    generalize LD t * nst (tbQ P t k) (2 ^ t) c₁.nmem = B at *
    generalize Cx P * potX P X = C1 at *
    generalize Cx P * potX P (fun t' k' ρ => X t' k' ρ ∨ (t' = t ∧ k' = k ∧ ρ = m)) = C2 at *
    omega
  · -- the target is settled
    refine spec_ifLtN_false (by rw [f192, hG₃.r110]; omega) ?_
    refine spec_skip hw₃ ⟨K, v, d, _, ⟨hw₃, hG₃, hX₃, hDa₃, kN, kR, kO,
      hS₂.xe_done fun y hy => by rw [hy, e3N]; omega, hR, hK0⟩, ?_⟩
    unfold pot
    rw [e3N, hpotS]
    generalize LD t * nst (tbQ P t k) (2 ^ t) c₂.nmem = A at *
    generalize LD t * nst (tbQ P t k) (2 ^ t) c₁.nmem = B at *
    generalize Cx P * potX P X = C1 at *
    generalize Cx P * potX P (fun t' k' ρ => X t' k' ρ ∨ (t' = t ∧ k' = k ∧ ρ = m)) = C2 at *
    omega

/-! ### The main loop -/

/-- The ghost state of the main loop: the run `(K, v, d)`, the popped key, the extracted rows. -/
abbrev GS : Type := ℕ × (ℕ → ℕ) × (ℕ → ℤ) × ℝ × (ℕ → ℕ → ℕ → Prop)

/-- **The state of the main loop.** -/
structure MI (P : Prm) (c₀ : Config) (g : GS) (c : Config) : Prop where
  wb : WordsBounded P.W c
  glob : Glob P c
  gx : GX P c
  data : Data P c
  keepN : ∀ r < 100, c.nreg r = c₀.nreg r
  keepR : ∀ r < 100, c.rreg r = c₀.rreg r
  out : c.output = c₀.output
  ms : MSt P g.1 g.2.1 g.2.2.1 g.2.2.2.1 F2 F1 F2 g.2.2.2.2 c.nmem c.rmem
  run : MRun P g.1 g.2.1 g.2.2.1
  r190 : c.nreg 190 = prV P c.nmem (wnV P c.nmem 1) +
    tPr P.bh c.nmem (tWn P.bh (2 ^ P.TB) c.nmem 1)
  root : g.1 = 0 → prV P c.nmem P.r = 1

/-- **One round of the main loop.** -/
theorem mBody_exec (hL : Lay P) (hDc : Crossing P.b P.D) (hF : Feas P) {c₀ : Config}
    (g : GS) (c : Config) (hI : MI P c₀ g c) (hlt : c.nreg 117 < c.nreg 190) :
    ∃ c' k, Exec I P.W mBody c c' k ∧
      ∃ g', MI P c₀ g' c' ∧ pot P g'.2.2.2.2 c'.nmem + k + 2 ≤ pot P g.2.2.2.2 c.nmem := by
  obtain ⟨K, v, d, κ, X⟩ := g
  obtain ⟨hc, hG, hX, hDa, hkN, hkR, hO, hS, hR, h190, -⟩ := hI
  simp only at hS hR h190 ⊢
  have hw := lay_w hL
  have hbw := bh_le_W hL
  have hW := hS.hp.win
  have hx := (hW.under 1 le_rfl (by omega)).1
  have hminV := (win_root hW (by omega)).2
  obtain ⟨hwl, hminB⟩ := win_root hS.bh.win Nat.one_le_two_pow
  have hpx1 := hS.hp.pr_le _ hx
  have hpw1 := hS.bh.pr _ hwl
  rw [hG.r117, h190] at hlt
  have hx' : c.nmem (P.wb + P.N + 1) < P.N := hx
  have hwl' : c.nmem (P.bh + 8 * 2 ^ P.TB + 2) < 2 ^ P.TB := by
    have := hwl; unfold tWn at this; simpa using this
  unfold mBody
  refine spec_seq ?_
  exec_block
  · rw [hG.r114, hG.r110]; omega
  · config_simp; rw [hG.r109, hG.r114, hG.r110]; omega
  · config_simp; rw [hX.r242, hG.r111]; omega
  · config_simp; rw [hX.r242, hG.r111, hG.r118]; omega
  · config_simp; rw [hX.r242, hG.r111, hG.r118, hX.r241]; omega
  generalize hc₁ : (Config.mk _ _ _ _ _ _ : Config) = c₁
  have hw₁ : WordsBounded P.W c₁ := hc₁ ▸ ‹_›
  have f180 : c₁.nreg 180 = wnV P c.nmem 1 := by
    rw [← hc₁]; config_simp; rw [hG.r114, hG.r110]; rfl
  have f192 : c₁.nreg 192 = prV P c.nmem (wnV P c.nmem 1) := by
    rw [← hc₁]; config_simp; rw [hG.r109, hG.r114, hG.r110]; rfl
  have r180 : c₁.rreg 180 = keyV P c.rmem (wnV P c.nmem 1) := by
    rw [← hc₁]; config_simp; rw [hG.r109, hG.r114, hG.r110]; rfl
  have f290 : c₁.nreg 290 = tWn P.bh (2 ^ P.TB) c.nmem 1 := by
    rw [← hc₁]; config_simp; rw [hX.r242, hG.r111]; rfl
  have f193 : c₁.nreg 193 = tPr P.bh c.nmem (tWn P.bh (2 ^ P.TB) c.nmem 1) := by
    rw [← hc₁]; config_simp; rw [hX.r242, hG.r111, hG.r118, hX.r241]
    unfold tPr tWn; congr 1; ring
  have r190 : c₁.rreg 190 = tKey P.bh c.rmem (tWn P.bh (2 ^ P.TB) c.nmem 1) := by
    rw [← hc₁]; config_simp; rw [hX.r242, hG.r111, hG.r118, hX.r241]
    unfold tKey tWn; congr 1; ring
  have fK : ∀ r, r ≠ 180 → r ≠ 191 → r ≠ 192 → r ≠ 193 → r ≠ 290 → c₁.nreg r = c.nreg r :=
    fun r h1 h2 h3 h4 h5 => by rw [← hc₁]; config_simp; upd_tac
  have fR : ∀ r, r ≠ 180 → r ≠ 190 → c₁.rreg r = c.rreg r := fun r h1 h2 => by
    rw [← hc₁]; config_simp; upd_tac
  have fN : c₁.nmem = c.nmem := by rw [← hc₁]
  have fM : c₁.rmem = c.rmem := by rw [← hc₁]
  have fO : c₁.output = c.output := by rw [← hc₁]
  have hG₁ : Glob P c₁ := hG.of fun r h1 h2 => fK r (by omega) (by omega) (by omega) (by omega)
    (by omega)
  have hX₁ : GX P c₁ := hX.of fun r h1 h2 => fK r (by omega) (by omega) (by omega) (by omega)
    (by omega)
  have hDa₁ : Data P c₁ := hDa.of hL (fun a _ => by rw [fN]) (fun a _ => by rw [fM])
  have hS₁ : MSt P K v d κ F2 F1 F2 X c₁.nmem c₁.rmem := by rw [fN, fM]; exact hS
  -- the end of a round
  have fin : ∀ (c₂ : Config) (k₂ : ℕ) (K' : ℕ) (v' : ℕ → ℕ) (d' : ℕ → ℤ) (κ' : ℝ)
      (X' : ℕ → ℕ → ℕ → Prop), Post P c₁ K' v' d' κ' X' c₂ →
      pot P X' c₂.nmem + k₂ + 23 ≤ pot P X c.nmem →
      ∃ c' k, Exec I P.W gflag c₂ c' k ∧ ∃ g', MI P c₀ g' c' ∧
        pot P g'.2.2.2.2 c'.nmem + (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + (k₂ + k)) +
          2 ≤ pot P X c.nmem := by
    intro c₂ k₂ K' v' d' κ' X' hP hpot
    refine spec_use (gflag_exec (I := I) hL c₂ hP.wb hP.glob hP.gx hP.ms.hp.win hP.ms.hp.pr_le
      hP.ms.bh) ?_
    intro c₃ k₃ hk₃ hw₃ ⟨h190₃, hK₃, hR₃, hN₃, hM₃, hO₃⟩
    refine ⟨(K', v', d', κ', X'), ⟨hw₃, hP.glob.of fun r h1 h2 => hK₃ r (by omega) (by omega)
      (by omega) (by omega), hP.gx.of fun r h1 h2 => hK₃ r (by omega) (by omega) (by omega)
      (by omega), hP.data.of hL (fun a _ => by rw [hN₃]) (fun a _ => by rw [hM₃]),
      fun r hr => ?_, fun r hr => ?_, ?_, by rw [hN₃, hM₃]; exact hP.ms, hP.run,
      by rw [h190₃, hN₃], fun h => absurd h (by have := hP.pos; simp only; omega)⟩, ?_⟩
    · rw [hK₃ r (by omega) (by omega) (by omega) (by omega), hP.keepN r hr,
        fK r (by omega) (by omega) (by omega) (by omega) (by omega)]; exact hkN r hr
    · rw [hR₃, hP.keepR r hr, fR r (by omega) (by omega)]; exact hkR r hr
    · rw [hO₃, hP.out, fO, hO]
    · simp only; rw [hN₃]; omega
  refine spec_seq ?_
  -- the four cases
  by_cases hpv : prV P c.nmem (wnV P c.nmem 1) = 1
  · by_cases hpb : tPr P.bh c.nmem (tWn P.bh (2 ^ P.TB) c.nmem 1) = 1
    · refine spec_ifLtN_false (by rw [f192, hG₁.r110, hpv]; omega) ?_
      refine spec_ifLtN_false (by rw [f193, hG₁.r110, hpb]; omega) ?_
      by_cases hlt' : tKey P.bh c.rmem (tWn P.bh (2 ^ P.TB) c.nmem 1) <
          keyV P c.rmem (wnV P c.nmem 1)
      · refine spec_ifLtR_true (by rw [r190, r180]; exact hlt') ?_
        obtain ⟨c₂, k₂, e₂, K', v', d', X', hP, hpot⟩ := bPop_exec (I := I) hL hDc hF c₁ hw₁ hG₁
          hX₁ hDa₁ hS₁ hR (by rw [f290, fN]) (by rw [fN]; exact hpb)
          (fun y hy hpy => by
            rw [fN, fM]; rw [fN] at hpy
            exact hlt'.le.trans (hminV y hy hpy).2)
        refine ⟨c₂, k₂, e₂, fin c₂ (k₂ + 1 + 2 + 2) K' v' d' _ X' hP (by rw [fN] at hpot; omega)⟩
      · refine spec_ifLtR_false (by rw [r190, r180]; exact hlt') ?_
        obtain ⟨c₂, k₂, e₂, dK, hP, hpot⟩ := vPop_exec (I := I) hL hDc hF c₁ hw₁ hG₁ hX₁ hDa₁ hS₁
          hR (by rw [f180, fN]) (by rw [fN]; exact hpv) (by rw [r180, fN, fM])
          (fun w hw hpw => by
            rw [fN, fM]; rw [fN] at hpw
            exact (not_lt.1 hlt').trans (hminB w hw hpw).2)
        refine ⟨c₂, k₂, e₂, fin c₂ (k₂ + 2 + 2 + 2) _ _ _ _ X hP (by rw [fN] at hpot; omega)⟩
    · refine spec_ifLtN_false (by rw [f192, hG₁.r110, hpv]; omega) ?_
      refine spec_ifLtN_true (by rw [f193, hG₁.r110]; omega) ?_
      obtain ⟨c₂, k₂, e₂, dK, hP, hpot⟩ := vPop_exec (I := I) hL hDc hF c₁ hw₁ hG₁ hX₁ hDa₁ hS₁
        hR (by rw [f180, fN]) (by rw [fN]; exact hpv) (by rw [r180, fN, fM])
        (fun w hw hpw => by
          rw [fN] at hpw
          exact absurd (hminB w hw hpw).1 hpb)
      refine ⟨c₂, k₂, e₂, fin c₂ (k₂ + 1 + 2) _ _ _ _ X hP (by rw [fN] at hpot; omega)⟩
  · have hpb : tPr P.bh c.nmem (tWn P.bh (2 ^ P.TB) c.nmem 1) = 1 := by omega
    refine spec_ifLtN_true (by rw [f192, hG₁.r110]; omega) ?_
    obtain ⟨c₂, k₂, e₂, K', v', d', X', hP, hpot⟩ := bPop_exec (I := I) hL hDc hF c₁ hw₁ hG₁
      hX₁ hDa₁ hS₁ hR (by rw [f290, fN]) (by rw [fN]; exact hpb)
      (fun y hy hpy => by
        rw [fN] at hpy
        exact absurd (hminV y hy hpy).1 hpv)
    refine ⟨c₂, k₂, e₂, fin c₂ (k₂ + 1) K' v' d' _ X' hP (by rw [fN] at hpot; omega)⟩

/-- **The main loop**: one round while one of the roots is present; at the end both heaps are
empty, so the run is closed under the arcs. -/
theorem mainLoop_exec (hL : Lay P) (hDc : Crossing P.b P.D) (hF : Feas P) {c₀ : Config}
    (g : GS) (c : Config) (hI : MI P c₀ g c) :
    ∃ c' k, Exec I P.W (.whileLtN 117 190 mBody) c c' k ∧ k ≤ pot P g.2.2.2.2 c.nmem + 2 ∧
      Glob P c' ∧ GX P c' ∧ Data P c' ∧ (∀ r < 100, c'.nreg r = c₀.nreg r) ∧
      (∀ r < 100, c'.rreg r = c₀.rreg r) ∧ c'.output = c₀.output ∧
      ∃ K v d, FRes P K v d c'.nmem c'.rmem := by
  obtain ⟨g', c', k, e, hI', hn, hk⟩ := Exec.whileLtN_ghost (P := I) (W := P.W) (a := 117)
    (b := 190) (body := mBody) (MI P c₀) (fun g c => pot P g.2.2.2.2 c.nmem)
    (fun _ _ h => h.wb)
    (fun g c hI hlt => by
      obtain ⟨c', k, e, g', h1, h2⟩ := mBody_exec hL hDc hF g c hI hlt
      exact ⟨g', c', k, e, h1, h2⟩) hI
  refine ⟨c', k, e, hk, hI'.glob, hI'.gx, hI'.data, hI'.keepN, hI'.keepR, hI'.out, g'.1, g'.2.1,
    g'.2.2.1, ?_⟩
  have hS := hI'.ms
  have hw := lay_w hL
  rw [hI'.glob.r117, hI'.r190] at hn
  have hW := hS.hp.win
  have hV : ∀ z < P.N, prV P c'.nmem z ≠ 1 := fun z hz hpz => by
    have := (win_root hW (by omega)).2 z hz hpz; omega
  have hB : ∀ w < 2 ^ P.TB, tPr P.bh c'.nmem w ≠ 1 := fun w hw' hpw => by
    have := (win_root hS.bh.win Nat.one_le_two_pow).2 w hw' hpw; omega
  refine ⟨hI'.run, Nat.pos_of_ne_zero fun h0 => hV _ hL.r_lt (hI'.root h0), hS.gh.vlt,
    fun i hi y ℓ ha => ?_, hS.gh.sf, hS.gh.dist⟩
  by_contra hc
  have hyN := ha.dst_lt hL
  have hys : sfV P c'.nmem y = 0 := by
    have := hS.hp.sf_le y hyN
    by_contra h'
    obtain ⟨j, hj, e⟩ := (hS.gh.sf y hyN).1 (by omega)
    exact hc ⟨j, hj, e.symm⟩
  rcases hS.cover hL hi ha hys with ⟨z, hz, hcl⟩ | ⟨w, hw', hpw, -⟩
  · exact hV z hz hcl.1
  · exact hB w hw' hpw

end FR

end Monge

end PlanarFlow
