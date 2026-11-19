module

public import PlanarFlow.NegSSSP.NdGather
public import PlanarFlow.NegSSSP.NSpecLeaf

/-!
# The node step: the children's outcomes combined

* `nd_none`: a child without a feasible potential gives none for the node.
* `ndComb N P₀ f₀ f₁` (`f₀` on the vertices of `P₀`, `f₁` elsewhere) and **`nd_comb_pot`**: when
  the two parts share no vertex (`bdry N P₀ P₁ = ∅`), the combination of feasible potentials of
  the parts is a feasible potential of `P₀ ∪ P₁`.
* `cg_child`: what `cgProg` reads from a child's outcome region (`Res … (some f)`): `0` off the
  child's vertices, `(f x + L).toNat + 1` on them.
* `ndCmbB`, **`ndCmb`** (registers `2487 … 2499`): for `v < w`, `F[v] := G₀[v] − 1` if
  `G₀[v] ≠ 0`, else `G₁[v] − 1`, and the count of `v` with `G₀[v] ≠ 0 ∧ G₁[v] ≠ 0` (straight
  line, `x / x` as the indicator of `x ≠ 0`); **`ndCmb_exec`** (`19 w + 6` steps).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace NegSSSP

namespace Frame

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs BKMNW Driver

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {g : GIds D V} {N : CombMap D V F}

/-! ### Semantics -/

theorem nd_none {P Q : Finset D} (hQ : Q ⊆ P) {ℓ : D → ℤ} (h : PotOut (pg N Q ℓ) none) :
    PotOut (pg N P ℓ) none :=
  not_pot_mono hQ h

/-- The combination of the potentials of the two parts. -/
noncomputable def ndComb (N : CombMap D V F) (P₀ : Finset D) (f₀ f₁ : V → ℤ) (x : V) : ℤ :=
  if x ∈ verts N P₀ then f₀ x else f₁ x

/-- **Parts without a shared vertex**: the combination of feasible potentials of the parts is a
feasible potential of the union. -/
theorem nd_comb_pot {P₀ P₁ : Finset D} (hb : bdry N P₀ P₁ = ∅) {ℓ : D → ℤ} {f₀ f₁ : V → ℤ}
    (h₀ : (pg N P₀ ℓ).IsPot f₀) (h₁ : (pg N P₁ ℓ).IsPot f₁) :
    (pg N (P₀ ∪ P₁) ℓ).IsPot (ndComb N P₀ f₀ f₁) := by
  rintro ⟨d, hd⟩
  show ndComb N P₀ f₀ f₁ (N.head d) ≤ ndComb N P₀ f₀ f₁ (N.tail d) + ℓ d
  rcases mem_union.1 hd with hd | hd
  · unfold ndComb
    rw [if_pos (head_mem_verts hd), if_pos (tail_mem_verts hd)]
    exact h₀ ⟨d, hd⟩
  · have hn : ∀ x ∈ verts N P₁, x ∉ verts N P₀ := fun x hx h => by
      have : x ∈ bdry N P₀ P₁ := mem_inter.2 ⟨h, hx⟩
      rw [hb] at this; simp at this
    unfold ndComb
    rw [if_neg (hn _ (head_mem_verts hd)), if_neg (hn _ (tail_mem_verts hd))]
    exact h₁ ⟨d, hd⟩

/-- **What `cgProg` reads from a child's outcome region.** -/
theorem cg_child {L w₀ : ℕ} {ι₀ : ℕ → V} {Pc : Finset D} {f : V → ℤ} {ID VL : ℕ → ℕ}
    (hι : ∀ u < w₀, ι₀ u ∈ verts N Pc ∧ ID u = g.gv (ι₀ u) ∧ VL u = (f (ι₀ u) + L).toNat)
    (hcov : ∀ x ∈ verts N Pc, ∃ u < w₀, ι₀ u = x) {o : ℕ} {x : V}
    (ho : (o = 0 ↔ ∀ u < w₀, ID u ≠ g.gv x) ∧ ∀ u < w₀, ID u = g.gv x → o = VL u + 1) :
    (o = 0 ↔ x ∉ verts N Pc) ∧ (x ∈ verts N Pc → o = (f x + L).toNat + 1) := by
  refine ⟨?_, fun hx => ?_⟩
  · rw [ho.1]
    constructor
    · intro h hx
      obtain ⟨u, hu, rfl⟩ := hcov x hx
      exact h u hu (hι u hu).2.1
    · intro h u hu e
      rw [(hι u hu).2.1] at e
      exact h (g.gv_inj e ▸ (hι u hu).1)
  · obtain ⟨u, hu, rfl⟩ := hcov x hx
    rw [ho.2 u hu (hι u hu).2.1, (hι u hu).2.2]

/-- The identifiers of a child's list are consistent with its values. -/
theorem cg_cons {L w₀ : ℕ} {ι₀ : ℕ → V} {Pc : Finset D} {f : V → ℤ} {ID VL : ℕ → ℕ}
    (hι : ∀ u < w₀, ι₀ u ∈ verts N Pc ∧ ID u = g.gv (ι₀ u) ∧ VL u = (f (ι₀ u) + L).toNat) :
    ∀ u < w₀, ∀ u' < w₀, ID u = ID u' → VL u = VL u' := fun u hu u' hu' e => by
  rw [(hι u hu).2.1, (hι u' hu').2.1] at e
  rw [(hι u hu).2.2, (hι u' hu').2.2, g.gv_inj e]

/-! ### The combination on the machine -/

/-- One vertex: `a = G₀[v]`, `b = G₁[v]`, `F[v] := ia (a − 1) + (1 − ia)(b − 1)` with
`ia = a / a`, `cnt += (a / a)(b / b)`. -/
def ndCmbB : Stmt := block [.addN 2499 2491 2494, .loadN 2497 2499, .addN 2499 2492 2494,
  .loadN 2498 2499, .divN 2489 2497 2497, .divN 2488 2498 2498, .mulN 2487 2489 2488,
  .addN 2496 2496 2487, .subN 2497 2497 2495, .subN 2498 2498 2495, .mulN 2497 2497 2489,
  .subN 2487 2495 2489, .mulN 2498 2498 2487, .addN 2497 2497 2498, .addN 2499 2493 2494,
  .storeN 2499 2497, .addN 2494 2494 2495]

/-- **The combination** (registers: `w = r2490`, `G₀ = r2491`, `G₁ = r2492`, `F = r2493`;
the count in `r2496`; scratch `2487 … 2489`, `2494 … 2499`). -/
def ndCmb : Stmt :=
  .seq (block [.constN 2495 1, .constN 2496 0, .constN 2494 0]) (.whileLtN 2494 2490 ndCmbB)

theorem ndCmb_natOnly : Klein.natOnly ndCmb = true := by decide

variable {I : Input} {W : ℕ}

/-- The value written for one vertex. -/
def cmbV (a b : ℕ) : ℕ := if a ≠ 0 then a - 1 else b - 1

theorem ndCmbB_exec (c : Config) (hc : WordsBounded W c) {G₀ G₁ Fb i a b n : ℕ}
    (r91 : c.nreg 2491 = G₀) (r92 : c.nreg 2492 = G₁) (r93 : c.nreg 2493 = Fb)
    (r94 : c.nreg 2494 = i) (r95 : c.nreg 2495 = 1) (r96 : c.nreg 2496 = n)
    (ma : c.nmem (G₀ + i) = a) (mb : c.nmem (G₁ + i) = b)
    (w1 : G₀ + i ≤ W) (w2 : G₁ + i ≤ W) (w3 : Fb + i ≤ W) (w4 : n + 1 ≤ W) (w5 : i + 1 ≤ W) :
    ∃ c'' t, Exec I W ndCmbB c c'' t ∧ t = 17 ∧ c''.nmem = upd c.nmem (Fb + i) (cmbV a b) ∧
      c''.nreg 2494 = i + 1 ∧ c''.nreg 2496 = n + (if a ≠ 0 ∧ b ≠ 0 then 1 else 0) ∧
      (∀ r, (r < 2487 ∨ (2489 < r ∧ r < 2494) ∨ r = 2495 ∨ 2499 < r) →
        c''.nreg r = c.nreg r) ∧
      c''.rreg = c.rreg ∧ c''.rmem = c.rmem ∧ c''.output = c.output := by
  have ha' : a / a = if a ≠ 0 then 1 else 0 := by
    rcases Nat.eq_zero_or_pos a with h | h
    · subst h; simp
    · rw [Nat.div_self h, if_pos (by omega)]
  have hb' : b / b = if b ≠ 0 then 1 else 0 := by
    rcases Nat.eq_zero_or_pos b with h | h
    · subst h; simp
    · rw [Nat.div_self h, if_pos (by omega)]
  have haW : a ≤ W := ma ▸ WordsBounded.nmem hc _
  have hbW : b ≤ W := mb ▸ WordsBounded.nmem hc _
  have p1 : a / a * (b / b) ≤ 1 := by
    rw [ha', hb']; split_ifs <;> omega
  have p2 : (a - 1) * (a / a) ≤ W := by rw [ha']; split_ifs <;> omega
  have p3 : (b - 1) * (1 - a / a) ≤ W := by rw [ha']; split_ifs <;> omega
  have p4 : (a - 1) * (a / a) + (b - 1) * (1 - a / a) = cmbV a b := by
    unfold cmbV; rw [ha']; split_ifs <;> simp
  have p5 : (a - 1) * (a / a) + (b - 1) * (1 - a / a) ≤ W := by
    rw [p4]; unfold cmbV; split_ifs <;> omega
  have p6 : a / a * (b / b) = if a ≠ 0 ∧ b ≠ 0 then 1 else 0 := by
    rw [ha', hb']
    by_cases h1 : a = 0 <;> by_cases h2 : b = 0 <;> simp [h1, h2]
  unfold ndCmbB
  exec_block
  all_goals try ((try config_simp); (try simp only [r91, r92, r93, r94, r95, r96, ma,
    mb]) <;> omega)
  refine ⟨rfl, ?_, ?_, ?_, fun r hr => ?_, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try (simp only [r91, r92, r93, r94, r95, r96, ma, mb])
  all_goals first | (rw [p4]; done) | (rw [p6]; done) | omega | (simp (disch := omega) only [upd_other])

/-- **The combination loop.** -/
theorem ndCmb_exec (c : Config) (hc : WordsBounded W c) {w G₀ G₁ Fb : ℕ}
    (r90 : c.nreg 2490 = w) (r91 : c.nreg 2491 = G₀) (r92 : c.nreg 2492 = G₁)
    (r93 : c.nreg 2493 = Fb) (w1 : G₀ + w ≤ W) (w2 : G₁ + w ≤ W) (w3 : Fb + w ≤ W)
    (w4 : w + 1 ≤ W) (d0 : Fb + w ≤ G₀ ∨ G₀ + w ≤ Fb) (d1 : Fb + w ≤ G₁ ∨ G₁ + w ≤ Fb) :
    ∃ c' t, Exec I W ndCmb c c' t ∧ t ≤ 19 * w + 5 ∧
      (∀ v < w, c'.nmem (Fb + v) = cmbV (c.nmem (G₀ + v)) (c.nmem (G₁ + v))) ∧
      c'.nreg 2496 = ((range w).filter fun v => c.nmem (G₀ + v) ≠ 0 ∧
        c.nmem (G₁ + v) ≠ 0).card ∧
      (∀ a, (a < Fb ∨ Fb + w ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, (r < 2487 ∨ (2489 < r ∧ r < 2494) ∨ 2499 < r) → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c₁, k₁, e₁, hk₁, g95, g96, g94, gn₁, gm₁, gr₁, grm₁, go₁⟩ : ∃ c₁ k₁,
      Exec I W (block [.constN 2495 1, .constN 2496 0, .constN 2494 0]) c c₁ k₁ ∧
      k₁ = 3 ∧ c₁.nreg 2495 = 1 ∧ c₁.nreg 2496 = 0 ∧ c₁.nreg 2494 = 0 ∧
      (∀ r, r ≠ 2494 → r ≠ 2495 → r ≠ 2496 → c₁.nreg r = c.nreg r) ∧
      c₁.nmem = c.nmem ∧ c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    exec_block
    all_goals try omega
    refine ⟨rfl, ?_, ?_, ?_, fun r h1 h2 h3 => ?_, rfl, rfl, rfl, rfl⟩
    all_goals config_simp
    simp only [upd_apply]; split_ifs <;> omega
  let J : ℕ → Config → Prop := fun i c' =>
    (∀ v < i, c'.nmem (Fb + v) = cmbV (c.nmem (G₀ + v)) (c.nmem (G₁ + v))) ∧
      c'.nreg 2496 = ((range i).filter fun v => c.nmem (G₀ + v) ≠ 0 ∧
        c.nmem (G₁ + v) ≠ 0).card ∧
      (∀ a, (a < Fb ∨ Fb + i ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, (r < 2487 ∨ (2489 < r ∧ r < 2494) ∨ r = 2495 ∨ 2499 < r) →
        c'.nreg r = c₁.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output
  obtain ⟨c₂, k₂, e₂, hk₂, -, hJ⟩ := forLoop_exec (P := I) (a := 2494) (bR := 2490)
    (body := ndCmbB) J (K := 17) (n := w) c₁ e₁.wb_right g94
    ((gn₁ 2490 (by omega) (by omega) (by omega)).trans r90)
    ⟨fun v hv => absurd hv (by omega), by rw [g96]; simp, fun a _ => by rw [gm₁],
      fun _ _ => rfl, gr₁, grm₁, go₁⟩
    (fun i c' hi hw ha hb hJ => by
      obtain ⟨j1, j2, j3, jn, jr, jrm, jo⟩ := hJ
      have q : ∀ r, r = 2491 ∨ r = 2492 ∨ r = 2493 → c'.nreg r = c.nreg r := fun r hr => by
        rw [jn r (by omega), gn₁ r (by omega) (by omega) (by omega)]
      have hcnt : ((range i).filter fun v => c.nmem (G₀ + v) ≠ 0 ∧
          c.nmem (G₁ + v) ≠ 0).card ≤ i := by
        have := card_filter_le (range i) (fun v => c.nmem (G₀ + v) ≠ 0 ∧ c.nmem (G₁ + v) ≠ 0)
        rw [card_range] at this; exact this
      obtain ⟨c'', t, ex, ht, hm, h94, h96, hn, hr, hrm, ho⟩ :=
        ndCmbB_exec (I := I) c' hw ((q 2491 (by omega)).trans r91)
          ((q 2492 (by omega)).trans r92) ((q 2493 (by omega)).trans r93) ha
          ((jn 2495 (by omega)).trans g95) j2 (j3 (G₀ + i) (by omega))
          (j3 (G₁ + i) (by omega)) (by omega) (by omega) (by omega) (by omega) (by omega)
      refine ⟨c'', t, ex, by omega, h94, (hn 2490 (by omega)).trans hb,
        ⟨fun v hv => ?_, ?_, fun a ha' => ?_, fun r hr' => (hn r (by omega)).trans (jn r hr'),
          by rw [hr, jr], by rw [hrm, jrm], by rw [ho, jo]⟩⟩
      · rw [hm, upd_apply]
        split_ifs with h
        · have : v = i := by omega
          subst this; rfl
        · exact j1 v (by omega)
      · rw [h96, range_add_one, filter_insert]
        by_cases h1 : c.nmem (G₀ + i) ≠ 0 ∧ c.nmem (G₁ + i) ≠ 0
        · rw [if_pos h1, if_pos h1, card_insert_of_notMem (by simp)]
        · rw [if_neg h1, if_neg h1]; rfl
      · rw [hm, upd_other _ _ _ (by omega)]; exact j3 a (by omega))
  obtain ⟨j1, j2, j3, jn, jr, jrm, jo⟩ := hJ
  refine ⟨c₂, k₁ + k₂, .seq e₁ e₂, by omega, j1, j2, j3, fun r hr => ?_, jr, jrm, jo⟩
  rw [jn r (by omega), gn₁ r (by omega) (by omega) (by omega)]

end Frame

end NegSSSP

end PlanarFlow
