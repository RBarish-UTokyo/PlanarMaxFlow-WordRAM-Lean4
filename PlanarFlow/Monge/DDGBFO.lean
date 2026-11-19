module

public import PlanarFlow.Monge.DDGBFOHead

/-!
# The levels of a round over a dense distance graph with missing arcs

The half blocks, blocks and levels of `PlanarFlow/Monge/DDGBF.lean` with the oracle `entO` and
the update `updBodyO` of `PlanarFlow/Monge/DDGBFOHead.lean` (the programs `halfO`, `blockBodyO`,
`levelBFO` have the structure of `half`, `blockBody`, `levelBF`), verified as in
`PlanarFlow/Monge/DDGBF2Round.lean` with the invariant `RoundGX` (only the arcs `X`). Each half
block of the level loop is the half block `hbOf` of its pairs (`hbOf_first`, `hbOf_second`), so
the static tables give the totally monotone matrix of the half block (`blkO_totMono`).

* `halfO_exec`: a half block, within `625 (nr + nc + 1)` steps;
* `blockBodyO_exec`, `levelBFO_exec`: a block, a level (`levelCostO b = 3766 b + 5`);
* `levelsO_exec`: **the levels of one round** relax every arc `i → j` with `X i j` in place,
  within `(levelCostO b + 2) (log₂ b + 1) + 2` steps.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace Monge

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

variable {b : ℕ} {X : ℕ → ℕ → Prop} {D : ℕ → ℕ → ℤ} {Q : Prop} {lo hi : ℕ → ℤ}
  {Vb eb pb : ℕ} {H : ℝ} {P : Input} {W : ℕ}

/-- The cost bound of a block of the level `s`. -/
def blockCostO (_b s : ℕ) : ℕ := 2 * (625 * (2 * s + 1)) + 14

/-- The cost of a half block of the level `s`. -/
lemma halfCostO_le {b s nr nc : ℕ} (h1 : nr ≤ s) (h2 : nc ≤ s) (_h3 : s ≤ b) (_hnr : 1 ≤ nr) :
    625 * (nr + nc + 1) ≤ 625 * (2 * s + 1) := by
  omega

/-- The cost bound of a level. -/
def levelCostO (b : ℕ) : ℕ := 3766 * b + 5

/-- The blocks of a level fit `levelCostO`. -/
lemma blocksO_le {b s : ℕ} (hs : 1 ≤ s) (hsb : s < b) :
    (blockCostO b s + 2) * ((b + s) / (2 * s)) + 5 ≤ levelCostO b := by
  unfold blockCostO levelCostO
  have h2 : s * ((b + s) / (2 * s)) ≤ b := by
    have := Nat.div_mul_le_self (b + s) (2 * s)
    have e : (b + s) / (2 * s) * (2 * s) = 2 * (s * ((b + s) / (2 * s))) := by ring
    omega
  have h1 : 2 * (625 * (2 * s + 1)) + 14 + 2 ≤ 3766 * s := by omega
  calc (2 * (625 * (2 * s + 1)) + 14 + 2) * ((b + s) / (2 * s)) + 5
      ≤ 3766 * s * ((b + s) / (2 * s)) + 5 := by
        have := Nat.mul_le_mul_right ((b + s) / (2 * s)) h1; omega
    _ = 3766 * (s * ((b + s) / (2 * s))) + 5 := by ring
    _ ≤ 3766 * b + 5 := by have := Nat.mul_le_mul_left 3766 h2; omega

/-! ### A half block -/

/-- **A half block** (`half_exec` with the oracle `entO`, the update `updBodyO`, the invariant
`RoundGX` and the memory frame). -/
theorem halfO_exec (hD : CrossingX b X D)
    (hH : ∀ s t, s < b → t < b → X s t → (D s t : ℝ) + b < H) (hL : LayO b Vb eb pb W)
    {C : ℕ → ℕ → Prop}
    {E₀ E : ℕ → ℤ} {r0 nr c1 nc : ℕ} (c : Config) (hc : WordsBounded W c)
    (hE : EnvO b Vb eb pb X D H c) (hV : Vals b eb E c)
    (hR : RoundGX b X D Q lo hi C E₀ E (c.nreg 30))
    (h24 : c.nreg 24 = r0) (h25 : c.nreg 25 = c1) (h60 : c.nreg 60 = nr) (h61 : c.nreg 61 = nc)
    (hnr : 1 ≤ nr) (hnc : 1 ≤ nc) (hnc' : nc ≤ c1) (hc1 : c1 ≤ b) (hr : r0 + nr ≤ b)
    (hsep : r0 + nr ≤ c1 - nc ∨ c1 ≤ r0)
    (hhb : ∀ ρ < nr, ∀ κ < nc, hbOf b (c1 - 1 - κ) (r0 + ρ) = (r0, nr, c1, nc)) :
    ∃ c' k', Exec P W halfO c c' k' ∧ k' ≤ 625 * (nr + nc + 1) ∧
      (EnvO b Vb eb pb X D H c' ∧
        (∃ E', Vals b eb E' c' ∧
          RoundGX b X D Q lo hi (fun i j => C i j ∨ HalfArcs r0 c1 nc nr i j) E₀ E' (c'.nreg 30)) ∧
        (∀ r < 60, r ≠ 26 → r ≠ 27 → r ≠ 28 → r ≠ 29 → r ≠ 30 → c'.nreg r = c.nreg r) ∧
        (∀ r < 60, r ≠ 20 → r ≠ 21 → c'.rreg r = c.rreg r) ∧ c'.output = c.output ∧
        (∀ a, pb + 5 * b + 1 < a → c'.nmem a = c.nmem a) ∧
        (∀ a, (pb + 5 * b + 1 < a ∧ a < eb) ∨ eb + b ≤ a → c'.rmem a = c.rmem a)) := by
  have hLw := hL.w
  have hpe := hL.pe
  have hed := hL.ed
  unfold halfO
  refine spec_seq ?_
  refine spec_instr (Exec.copyN hc 62 4) fun hw₁ => ?_
  refine spec_seq ?_
  have hEa : EnvO b Vb eb pb X D H { c with nreg := upd c.nreg 62 (c.nreg 4) } :=
    hE.of (fun r hr => by config_simp; rw [upd_other _ _ _ (by omega)]) rfl (fun _ _ => rfl)
      (fun _ _ => rfl)
  have hTM : IsTotMono nr nc (blkO X D H E r0 nr c1 nc) :=
    blkO_totMono hD hH hR.nonpos hnc' hc1 hr hsep
  refine spec_use (smawk_exec (entO_exec (P := P) hL hEa hV (by config_simp; exact h24)
    (by config_simp; exact h25) hnc' hc1 hr hsep hhb) hTM (by omega) (by omega) (by omega) hw₁
    (by config_simp; exact h60) (by config_simp; exact h61)
    (by config_simp; exact hE.r4)) ?_
  intro c₂ k₂ hk₂ hw₂ ⟨⟨a1, a2, a3, a4, a5⟩, g60, g61, g62, hres⟩
  refine spec_seq ?_
  refine spec_instr (Exec.constN hw₂ 26 0 (by omega)) fun hw₃ => ?_
  have n₁ : ∀ r < 60, r ≠ 26 →
      ({ c₂ with nreg := upd c₂.nreg 26 0 } : Config).nreg r = c.nreg r :=
    fun r hr h => by
      config_simp; rw [upd_other _ _ _ h, a1 r hr]; config_simp; rw [upd_other _ _ _ (by omega)]
  have hE₁ : EnvO b Vb eb pb X D H ({ c₂ with nreg := upd c₂.nreg 26 0 } : Config) :=
    hE.of (fun r hr => n₁ r (by omega) (by omega)) (a2 10 (by omega))
      (fun a ha => a4 a (Or.inr (by omega))) (fun a ha => a3 a (Or.inr (by omega)))
  have hV₁ : Vals b eb E ({ c₂ with nreg := upd c₂.nreg 26 0 } : Config) :=
    fun v hv => (a4 _ (Or.inr (by omega))).trans (hV v hv)
  refine spec_while
    (IUpO b Vb eb X D W Q lo hi C E₀ E r0 nr c1 nc { c₂ with nreg := upd c₂.nreg 26 0 })
    (fun c => 22 * (nr - c.nreg 26)) (fun c h => h.wb)
    (fun c' hc' hlt' => updBodyO_exec hH hL hE₁ (by rw [n₁ 24 (by omega) (by omega), h24])
      (by rw [n₁ 25 (by omega) (by omega), h25])
      (by config_simp; rw [g60]) hnc hnc' hc1 hr hsep hR.nonpos (fun ρ hρ =>
        ⟨by config_simp; exact (hres ρ hρ).1, by config_simp; exact (hres ρ hρ).2⟩) c' hc' hlt')
    ⟨hw₃, fun _ _ _ _ _ _ => rfl, fun _ _ _ => rfl, rfl, fun _ _ => rfl, rfl,
      by config_simp; omega, E, hV₁, ?_, fun _ _ _ => rfl⟩ ?_
  · rw [n₁ 30 (by omega) (by omega)]
    refine hR.mono fun i j _ _ _ _ hc => ?_
    rcases hc with hc | ⟨-, -, h3, h4⟩
    · exact hc
    · config_simp at h4; omega
  intro c₃ k₃ hI hn hk₃
  have h26 : c₃.nreg 26 = nr := by
    have := hI.ρ
    rw [hI.nreg 60 (by omega) (by omega) (by omega) (by omega) (by omega)] at hn
    config_simp at hn; rw [g60] at hn; omega
  obtain ⟨E', hV', hR', -⟩ := hI.vals
  rw [h26] at hR'
  have hK : 4 * nr + nc + 1 ≤ 5 * b + 1 := by omega
  refine ⟨?_, hE₁.of (fun r hr => hI.nreg r (by omega) (by omega) (by omega) (by omega)
      (by omega)) (hI.rreg 10 (by omega) (by omega)) (fun a ha => hI.rmem a (Or.inr (by omega)))
    (fun a ha => by rw [hI.nmem]),
    ⟨E', hV', hR'⟩, fun r hr a b' d e f => ?_, fun r hr h1 h2 => ?_, ?_, fun a ha => ?_,
    fun a ha => ?_⟩
  · beta_reduce at hk₃
    config_simp at hk₃
    omega
  · rw [hI.nreg r a b' d e f]; exact n₁ r hr a
  · rw [hI.rreg r h1 h2]; config_simp; rw [a2 r hr]
  · rw [hI.out]; config_simp; rw [a5]
  · rw [congrFun hI.nmem a]; config_simp; rw [a3 a (Or.inr (by omega))]
  · rw [hI.rmem a (by omega)]; config_simp; rw [a4 a (Or.inr (by omega))]

/-! ### A block -/

/-- The state between the blocks of the level `s` of a round (`IB` with the invariant `RoundGX`
and the frame `Frm` from `c₀`). -/
structure IBO (b Vb eb pb : ℕ) (X : ℕ → ℕ → Prop) (D : ℕ → ℕ → ℤ) (H : ℝ) (W : ℕ) (Q : Prop)
    (lo hi : ℕ → ℤ)
    (E₀ : ℕ → ℤ) (s : ℕ) (c₀ c : Config) : Prop where
  wb : WordsBounded W c
  env : EnvO b Vb eb pb X D H c
  frm : Frm b eb pb c₀ c
  r20 : c.nreg 20 = s
  base : ∃ q, c.nreg 21 = 2 * s * q
  r22 : c.nreg 22 = c.nreg 21 + s
  basele : c.nreg 21 ≤ b + s
  vals : ∃ E, Vals b eb E c ∧ RoundGX b X D Q lo hi (Cov s (c.nreg 21)) E₀ E (c.nreg 30)

/-- A block of the level `s` (`blockBody_exec` with the invariant `RoundGX` and the frame). -/
theorem blockBodyO_exec (hD : CrossingX b X D)
    (hH : ∀ s t, s < b → t < b → X s t → (D s t : ℝ) + b < H) (hL : LayO b Vb eb pb W)
    {E₀ : ℕ → ℤ} {s : ℕ}
    {c₀ : Config} (hs : 1 ≤ s) {T : ℕ} (hT : s = 2 ^ T) (hsb : s < b) (c : Config)
    (hI : IBO b Vb eb pb X D H W Q lo hi E₀ s c₀ c) (hlt : c.nreg 22 < c.nreg 1) :
    ∃ c' k', Exec P W blockBodyO c c' k' ∧ IBO b Vb eb pb X D H W Q lo hi E₀ s c₀ c' ∧
      (blockCostO b s + 2) * ((b + s - c'.nreg 21) / (2 * s)) + k' + 2 ≤
        (blockCostO b s + 2) * ((b + s - c.nreg 21) / (2 * s)) := by
  have hc := hI.wb
  have hE := hI.env
  have hLw := hL.w
  have hpe := hL.pe
  have hed := hL.ed
  rw [hI.r22, hE.r1] at hlt
  obtain ⟨q, hq⟩ := hI.base
  generalize hbase : c.nreg 21 = base at hq hlt
  obtain ⟨E, hV, hR⟩ := hI.vals
  rw [hbase] at hR
  have g20 := hI.r20
  have g22 : c.nreg 22 = base + s := by rw [hI.r22, hbase]
  unfold blockBodyO
  refine spec_seq ?_
  refine spec_instr (Exec.addN hc 23 22 20 (by rw [g22, g20]; omega)) fun hw₁ => ?_
  refine spec_seq ?_
  refine spec_use (minS_exec _ hw₁) ?_
  intro c₂ k₂ hk₂ hw₂ ⟨h23, hn₂, hr₂, hnm₂, hrm₂, ho₂⟩
  config_simp at h23
  rw [g22, g20, hE.r1] at h23
  generalize hrend : min (base + s + s) b = rend at h23
  have hrend1 : base + s < rend := by rw [← hrend]; omega
  have hrend2 : rend ≤ b := by rw [← hrend]; omega
  have hrend3 : rend ≤ base + 2 * s := by rw [← hrend]; omega
  have e₂ : ∀ r, r ≠ 23 → c₂.nreg r = c.nreg r := fun r hr => by
    rw [hn₂ r hr]; config_simp; rw [upd_other _ _ _ hr]
  have hE₂ : EnvO b Vb eb pb X D H c₂ :=
    hE.of (fun r hr => e₂ r (by omega)) (by rw [hr₂]) (fun a _ => by rw [hrm₂])
      (fun a _ => by rw [hnm₂])
  -- the first half: from `[base, base + s)` to `[base + s, rend)`
  refine spec_seq ?_
  exec_block
  refine spec_seq ?_
  refine spec_use (halfO_exec (P := P) hD hH hL (C := Cov s base) (r0 := base + s) (c1 := base + s)
    (nr := rend - (base + s)) (nc := s) _ ‹_›
    (hE₂.of (fun r hr => by config_simp; upd_tac) rfl (fun _ _ => rfl) (fun _ _ => rfl))
    (fun v hv => by config_simp; rw [hrm₂]; exact hV v hv)
    (by config_simp; rw [e₂ 30 (by omega)]; exact hR)
    (by config_simp; rw [e₂ 22 (by omega), g22])
    (by config_simp; rw [e₂ 22 (by omega), g22])
    (by config_simp; rw [h23, e₂ 22 (by omega), g22])
    (by config_simp; rw [e₂ 20 (by omega), g20])
    (by omega) hs (by omega) (by omega) (by omega) (Or.inr le_rfl)
    (fun ρ hρ κ hκ => by
      have := hbOf_first (b := b) hT hq (s := base + s - 1 - κ) (t := base + s + ρ) (by omega)
        (by omega) (by omega) (by rw [hrend]; omega)
      rwa [hrend] at this)) ?_
  intro c₃ k₃ hk₃ hw₃ ⟨hE₃, ⟨E₃, hV₃, hR₃⟩, hn₃, hr₃, ho₃, hnm₃, hrm₃⟩
  have e₃ : ∀ r < 60, r ≠ 23 → r ≠ 24 → r ≠ 25 → r ≠ 26 → r ≠ 27 → r ≠ 28 → r ≠ 29 → r ≠ 30 →
      c₃.nreg r = c.nreg r := fun r hr a1 a2 a3 a4 a5 a6 a7 a8 => by
    rw [hn₃ r hr a4 a5 a6 a7 a8]; config_simp
    simp only [upd_apply]; split_ifs <;> first | omega | exact e₂ r a1
  have g23₃ : c₃.nreg 23 = rend := by
    rw [hn₃ 23 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
    config_simp; exact h23
  -- the second half: from `[base + s, rend)` to `[base, base + s)`
  refine spec_seq ?_
  exec_block
  refine spec_seq ?_
  refine spec_use (halfO_exec (P := P) hD hH hL (r0 := base) (c1 := rend) (nr := s)
    (nc := rend - (base + s)) _ ‹_›
    (hE₃.of (fun r hr => by config_simp; upd_tac) rfl (fun _ _ => rfl) (fun _ _ => rfl))
    (fun v hv => by config_simp; exact hV₃ v hv)
    (by config_simp; exact hR₃)
    (by config_simp; rw [e₃ 21 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega), hbase])
    (by config_simp; exact g23₃)
    (by config_simp; rw [e₃ 20 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega), g20])
    (by config_simp; rw [g23₃, e₃ 22 (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega), g22])
    hs (by omega) (by omega) hrend2 (by omega) (Or.inl (by omega))
    (fun ρ hρ κ hκ => by
      have := hbOf_second (b := b) hT hq (s := rend - 1 - κ) (t := base + ρ) (by omega)
        (by omega) (by omega) (by rw [hrend]; omega)
      rwa [hrend] at this)) ?_
  intro c₄ k₄ hk₄ hw₄ ⟨hE₄, ⟨E₄, hV₄, hR₄⟩, hn₄, hr₄, ho₄, hnm₄, hrm₄⟩
  have e₄ : ∀ r < 60, r ≠ 23 → r ≠ 24 → r ≠ 25 → r ≠ 26 → r ≠ 27 → r ≠ 28 → r ≠ 29 → r ≠ 30 →
      r ≠ 60 → r ≠ 61 → c₄.nreg r = c.nreg r := fun r hr a1 a2 a3 a4 a5 a6 a7 a8 _ _ => by
    rw [hn₄ r hr a4 a5 a6 a7 a8]; config_simp
    simp only [upd_apply]; split_ifs <;> first | omega | exact e₃ r hr a1 a2 a3 a4 a5 a6 a7 a8
  have g20₄ : c₄.nreg 20 = s := by
    rw [e₄ 20 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega), g20]
  have g21₄ : c₄.nreg 21 = base := by
    rw [e₄ 21 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega), hbase]
  -- the frame of the two halves
  have hF₄ : Frm b eb pb c c₄ := by
    refine ⟨fun r hr h => e₄ r hr (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega), fun r hr h1 h2 => ?_,
      fun a ha => ?_, fun a ha => ?_, ?_⟩
    · rw [hr₄ r hr h1 h2]; config_simp; rw [hr₃ r hr h1 h2]; config_simp; rw [hr₂]
    · rw [hnm₄ a ha]; config_simp; rw [hnm₃ a ha]; config_simp; rw [hnm₂]
    · rw [hrm₄ a ha]; config_simp; rw [hrm₃ a ha]; config_simp; rw [hrm₂]
    · rw [ho₄]; config_simp; rw [ho₃]; config_simp; rw [ho₂]
  -- the next block
  exec_block
  · rw [g21₄, g20₄]; omega
  · config_simp; rw [g21₄, g20₄]; omega
  · config_simp; rw [g21₄, g20₄]; omega
  refine ⟨⟨‹_›, hE₄.of (fun r hr => by config_simp; upd_tac) rfl (fun _ _ => rfl) (fun _ _ => rfl),
    hI.frm.trans (hF₄.trans (Frm.of_regs (fun r hr h => ?_) rfl rfl rfl rfl)), ?_,
    ⟨q + 1, ?_⟩, ?_, ?_, ⟨E₄, fun v hv => by config_simp; exact hV₄ v hv, ?_⟩⟩, ?_⟩
  · config_simp; simp only [upd_apply]; split_ifs <;> omega
  · config_simp; exact g20₄
  · config_simp; rw [g21₄, g20₄, hq]; ring
  · config_simp; rw [g20₄]
  · config_simp; rw [g21₄, g20₄]; omega
  · config_simp; rw [g21₄, g20₄]
    refine hR₄.mono fun i j hi hj hij _ hc => ?_
    rw [show base + s + s = 2 * s * q + 2 * s by rw [hq]; ring] at hc
    rcases cov_step (by omega) hc with hc | hc
    · rw [← hq] at hc; exact Or.inl (Or.inl hc)
    · rw [← hq] at hc
      rcases hc with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩
      · exact Or.inl (Or.inr ⟨by omega, by omega, by omega, by omega⟩)
      · exact Or.inr ⟨by omega, by omega, by omega, by omega⟩
  · -- the cost
    config_simp; rw [g21₄, g20₄]
    have hb1 := halfCostO_le (b := b) (s := s) (nr := rend - (base + s)) (nc := s) (by omega)
      le_rfl hsb.le (by omega)
    have hb2 := halfCostO_le (b := b) (s := s) (nr := s) (nc := rend - (base + s)) le_rfl
      (by omega) hsb.le hs
    have hμ : (b + s - base) / (2 * s) = (b + s - (base + s + s)) / (2 * s) + 1 := by
      rw [show b + s - base = b + s - (base + s + s) + 2 * s by omega,
        Nat.add_div_right _ (by omega)]
    rw [hμ, Nat.mul_add, Nat.mul_one]
    generalize (blockCostO b s + 2) * ((b + s - (base + s + s)) / (2 * s)) = Y
    have hB : blockCostO b s = 2 * (625 * (2 * s + 1)) + 14 := rfl
    rw [hB]
    generalize hx : rend - (base + s) = x at hb1 hb2 ⊢
    omega

/-! ### A level -/

/-- The state between the levels of a round (`IL` with the invariant `RoundGX` and the frame
`Frm` from `c₀`). -/
structure ILO (b Vb eb pb : ℕ) (X : ℕ → ℕ → Prop) (D : ℕ → ℕ → ℤ) (H : ℝ) (W : ℕ) (Q : Prop)
    (lo hi : ℕ → ℤ)
    (E₀ : ℕ → ℤ) (c₀ c : Config) : Prop where
  wb : WordsBounded W c
  env : EnvO b Vb eb pb X D H c
  frm : Frm b eb pb c₀ c
  pow : ∃ t, c.nreg 20 = 2 ^ t
  sle : c.nreg 20 ≤ 2 * b + 1
  vals : ∃ E, Vals b eb E c ∧ RoundGX b X D Q lo hi (Cov (c.nreg 20) 0) E₀ E (c.nreg 30)

/-- A level of a round (`levelBF_exec` with the invariant `RoundGX` and the frame). -/
theorem levelBFO_exec (hD : CrossingX b X D)
    (hH : ∀ s t, s < b → t < b → X s t → (D s t : ℝ) + b < H) (hL : LayO b Vb eb pb W) {E₀ : ℕ → ℤ}
    {c₀ : Config} (c : Config) (hI : ILO b Vb eb pb X D H W Q lo hi E₀ c₀ c)
    (hlt : c.nreg 20 < c.nreg 1) :
    ∃ c' k', Exec P W levelBFO c c' k' ∧ ILO b Vb eb pb X D H W Q lo hi E₀ c₀ c' ∧
      (levelCostO b + 2) * (Nat.log 2 b + 1 - Nat.log 2 (c'.nreg 20)) + k' + 2 ≤
        (levelCostO b + 2) * (Nat.log 2 b + 1 - Nat.log 2 (c.nreg 20)) := by
  have hc := hI.wb
  have hE := hI.env
  have hLw := hL.w
  rw [hE.r1] at hlt
  obtain ⟨t, ht⟩ := hI.pow
  generalize hs : c.nreg 20 = s at ht hlt
  have hs1 : 1 ≤ s := by rw [ht]; exact Nat.one_le_two_pow
  obtain ⟨E, hV, hR⟩ := hI.vals
  rw [hs] at hR
  unfold levelBFO
  refine spec_seq ?_
  exec_block
  · omega
  refine spec_seq ?_
  refine spec_while (IBO b Vb eb pb X D H W Q lo hi E₀ s c₀)
    (fun c => (blockCostO b s + 2) * ((b + s - c.nreg 21) / (2 * s))) (fun c h => h.wb)
    (fun c' hc' hlt' => blockBodyO_exec hD hH hL hs1 ht hlt c' hc' hlt')
    ⟨‹_›, hE.of (fun r hr => by config_simp; upd_tac) rfl (fun _ _ => rfl) (fun _ _ => rfl),
      hI.frm.trans (Frm.of_regs (fun r hr h => by config_simp; upd_tac) rfl rfl rfl rfl),
      by config_simp; exact hs,
      ⟨0, by config_simp; ring⟩, by config_simp; rw [hs], by config_simp; omega,
      ⟨E, hV, by config_simp; exact hR⟩⟩ ?_
  intro c₂ k₂ hI₂ hn₂ hk₂
  have hw₂ := hI₂.wb
  have g20 := hI₂.r20
  have hend : b ≤ c₂.nreg 21 + s := by
    rw [hI₂.r22, hI₂.env.r1] at hn₂; omega
  refine spec_instr (Exec.addN hw₂ 20 20 20 (by rw [g20]; omega)) fun hw₃ => ?_
  obtain ⟨E₂, hV₂, hR₂⟩ := hI₂.vals
  refine ⟨⟨hw₃, hI₂.env.of (fun r hr => by config_simp; upd_tac) rfl (fun _ _ => rfl)
      (fun _ _ => rfl),
    hI₂.frm.trans (Frm.of_regs (fun r hr h => by config_simp; upd_tac) rfl rfl rfl rfl),
    ⟨t + 1, by config_simp; rw [g20, ht, pow_succ]; ring⟩, by config_simp; rw [g20]; omega,
    ⟨E₂, hV₂, ?_⟩⟩, ?_⟩
  · config_simp; rw [g20]
    refine hR₂.mono fun i j hi hj hij _ hc => ?_
    exact cov_level ht hend hi hj (by rw [show s + s = 2 * s by ring] at hc; exact hc)
  · config_simp; rw [g20]
    beta_reduce at hk₂
    config_simp at hk₂
    rw [Nat.sub_zero] at hk₂
    have hl1 : Nat.log 2 (s + s) = Nat.log 2 s + 1 := by
      rw [show s + s = s * 2 by ring, Nat.log_mul_base (by norm_num) (by omega)]
    have hl2 : Nat.log 2 s ≤ Nat.log 2 b := Nat.log_mono_right hlt.le
    rw [hl1]
    have hb := blocksO_le hs1 hlt
    have := mul_pred_add (a := levelCostO b + 2) (x := Nat.log 2 b + 1 - Nat.log 2 s) (by omega)
    rw [show Nat.log 2 b + 1 - Nat.log 2 s - 1 = Nat.log 2 b + 1 - (Nat.log 2 s + 1) by omega]
      at this
    omega

/-! ### The levels of a round -/

/-- **The levels of one round of relaxations by `D`**: started with `r20 = 1`, the flag
`r30 = 0` and the values `E` (between `lo` and `hi` under `Q`, `lo` a feasible potential of `D`
under `Q`), the loop `whileLtN 20 1 levelBF` relaxes every arc `i → j` (`i ≠ j`) of `D` in place
within `(levelCostO b + 2) (log₂ b + 1) + 2` steps. -/
theorem levelsO_exec (hD : CrossingX b X D)
    (hH : ∀ s t, s < b → t < b → X s t → (D s t : ℝ) + b < H) (hL : LayO b Vb eb pb W)
    {E : ℕ → ℤ} (c : Config)
    (hc : WordsBounded W c) (hE : EnvO b Vb eb pb X D H c) (hV : Vals b eb E c)
    (h20 : c.nreg 20 = 1) (h30 : c.nreg 30 = 0)
    (htop : ∀ v < b, E v ≤ 0)
    (hpot : Q → ∀ i j, i < b → j < b → i ≠ j → X i j → lo j ≤ lo i + D i j)
    (hS : Q → ∀ v < b, lo v ≤ E v ∧ E v ≤ hi v) :
    ∃ c' k, Exec P W (.whileLtN 20 1 levelBFO) c c' k ∧
      k ≤ (levelCostO b + 2) * (Nat.log 2 b + 1) + 2 ∧
      (Frm b eb pb c c' ∧ EnvO b Vb eb pb X D H c' ∧
        ∃ E', Vals b eb E' c' ∧ RoundGX b X D Q lo hi (fun _ _ => True) E E' (c'.nreg 30)) := by
  refine spec_while (ILO b Vb eb pb X D H W Q lo hi E c)
    (fun c => (levelCostO b + 2) * (Nat.log 2 b + 1 - Nat.log 2 (c.nreg 20))) (fun c h => h.wb)
    (fun c' hc' hlt' => levelBFO_exec hD hH hL c' hc' hlt')
    ⟨hc, hE, Frm.refl _ _ _ _, ⟨0, by rw [h20]; rfl⟩, by rw [h20]; omega,
      ⟨E, hV, by
        rw [h20, h30]
        exact (RoundGX.start htop hpot hS).mono fun i j _ _ _ _ hc => not_cov_one_zero hc⟩⟩ ?_
  intro c₂ k₂ hI₂ hn₂ hk₂
  rw [hI₂.env.r1] at hn₂
  obtain ⟨E₂, hV₂, hR₂⟩ := hI₂.vals
  refine ⟨?_, hI₂.frm, hI₂.env, E₂, hV₂,
    hR₂.mono (C' := fun _ _ => True) fun i j hi hj hij _ _ => cov_all (by omega) hij hi hj⟩
  rw [h20, show Nat.log 2 1 = 0 from Nat.log_one_right 2, Nat.sub_zero] at hk₂
  exact hk₂

end Monge

end PlanarFlow
