module

public import PlanarFlow.Monge.PrepP3

/-!
# Building the tables of a dense distance graph with missing arcs: the machine pass

**`prepO`** computes, from the plain encoding of a dense distance graph with missing arcs (the
arc flags `finB X s t` at `Fb + s b + t`, the lengths `D s t` at `Db + s b + t`, `InP`), the
static tables `tVal b X D (Hb b D)`, `tMul b X`, `finB X` read by `PlanarFlow.Monge.bfDDG2O` at
`Vb + 2 (s b + t)`, for all pairs `s ≠ t` (`prepO_exec`, within `prepCost b` steps, `O(b² log b)`):
the bound `Hb b D` (`hProg`), then for each level `sz = 1, 2, 4, … < b` three passes over the
targets (`pass1`, `pass2`, `pass3`): the first arc column and the genuine flag of each row, the
standing row, the entries of the pairs of the level (`levelP_exec`). Every pair `s ≠ t` is
written at its level `2 ^ levOf s t` (`lev_range`), where its half block is that of the level
loop of `bfDDG2O` (`hbOf_eq_hbT`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace Monge

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs NegSSSP Finset

attribute [local instance] Classical.propDecidable

/-- Pass 3 of a level: all the targets. -/
def pass3 : Stmt := .seq (.instr (.constN 45 0)) (.whileLtN 45 1 p3Body)

variable {b Vb Db Fb Sb W : ℕ} {X : ℕ → ℕ → Prop} {D : ℕ → ℕ → ℤ} {P : Input}

/-- The pairs of the level `sz` with their target below `t`. -/
def LvlP (b sz t : ℕ) (s t' : ℕ) : Prop := t' < t ∧ SrcP b sz t' (hbT b sz t').2.2.2 s

/-- The state of pass 3 from `c₀`. -/
structure IP3 (b Vb Db Fb Sb W : ℕ) (X : ℕ → ℕ → Prop) (D : ℕ → ℕ → ℤ) (H : ℝ) (sz : ℕ)
    (Pr : ℕ → ℕ → Prop) (c₀ c : Config) : Prop where
  wb : WordsBounded W c
  inp : InP b Vb Db Fb Sb X D c
  frm : FrP b Vb Sb c₀ c
  r44 : c.nreg 44 = sz
  le : c.nreg 45 ≤ b
  r40 : c.rreg 40 = H
  r42 : c.rreg 42 = 1
  mem : ∀ a, (a < Vb ∨ Vb + 2 * (b * b) ≤ a) → c.nmem a = c₀.nmem a ∧ c.rmem a = c₀.rmem a
  tab : TabOK b Vb X D H (fun s t => Pr s t ∨ LvlP b sz (c.nreg 45) s t) c

/-- **Pass 3 of a level.** -/
theorem pass3_exec (hL : LayP b Vb Db Fb Sb W) {H : ℝ} {sz T : ℕ} (hT : sz = 2 ^ T)
    (hszb : sz ≤ b) {Pr : ℕ → ℕ → Prop} (c : Config) (hc : WordsBounded W c)
    (hI : InP b Vb Db Fb Sb X D c) (h44 : c.nreg 44 = sz) (h40 : c.rreg 40 = H)
    (h42 : c.rreg 42 = 1)
    (hR : ∀ t < b, 0 < (hbT b sz t).2.2.2 → c.nmem (Sb + b + t) = Rv b X sz t)
    (hLv : ∀ t' < b, c.nmem (Sb + t') = Lv b X sz t') (htab : TabOK b Vb X D H Pr c) :
    ∃ c' k, Exec P W pass3 c c' k ∧ k ≤ (32 * sz + 22) * b + 3 ∧
      (FrP b Vb Sb c c' ∧ InP b Vb Db Fb Sb X D c' ∧ c'.nreg 44 = sz ∧ c'.rreg 40 = H ∧
        c'.rreg 42 = 1 ∧
        (∀ a, (a < Vb ∨ Vb + 2 * (b * b) ≤ a) → c'.nmem a = c.nmem a ∧ c'.rmem a = c.rmem a) ∧
        TabOK b Vb X D H (fun s t => Pr s t ∨ LvlP b sz b s t) c') := by
  have hw := hL.w; have hsd := hL.sd; have hdv := hL.dv
  unfold pass3
  refine spec_seq ?_
  refine spec_instr (Exec.constN hc 45 0 (by omega)) fun hw₁ => ?_
  have hF₁ : FrP b Vb Sb c { c with nreg := upd c.nreg 45 0 } :=
    ⟨fun r hr => by config_simp; rw [upd_other _ _ _ (by omega)], fun _ _ => rfl, fun _ _ => rfl,
      fun _ _ => rfl, rfl⟩
  refine spec_while (IP3 b Vb Db Fb Sb W X D H sz Pr c) (fun c => (32 * sz + 22) * (b - c.nreg 45))
    (fun c h => h.wb) ?_ ⟨hw₁, hI.of hL hF₁, hF₁, by config_simp; exact h44,
      by config_simp; omega, h40, h42, fun _ _ => ⟨rfl, rfl⟩,
      htab.mono fun s t h => by
        rcases h with h | ⟨h, -⟩
        · exact h
        · config_simp at h; omega⟩ ?_
  · intro c₁ hI₁ hlt
    rw [hI₁.inp.r1] at hlt
    generalize ht : c₁.nreg 45 = t at hlt
    have htab₁ := hI₁.tab
    rw [ht] at htab₁
    obtain ⟨c₂, k, hex, hk, hF, h44', h45', h40', h42', hmem, htab₂⟩ :=
      p3Body_exec (P := P) hL hT hszb c₁ hI₁.wb hI₁.inp hI₁.r44 ht hlt hI₁.r40 hI₁.r42
        (fun hnc => by rw [(hI₁.mem _ (Or.inl (by omega))).1]; exact hR t hlt hnc)
        (fun t' ht' => by rw [(hI₁.mem _ (Or.inl (by omega))).1]; exact hLv t' ht') htab₁
    refine ⟨c₂, k, hex, ⟨hex.wb_right, hI₁.inp.of hL hF, hI₁.frm.trans hF, h44', by omega, h40',
      h42', fun a ha => ?_, ?_⟩, ?_⟩
    · obtain ⟨e1, e2⟩ := hmem a ha; obtain ⟨f1, f2⟩ := hI₁.mem a ha
      exact ⟨e1.trans f1, e2.trans f2⟩
    · rw [h45']
      refine htab₂.mono fun s t' h => ?_
      rcases h with h | ⟨h1, h2⟩
      · exact Or.inl (Or.inl h)
      · rcases Nat.lt_or_ge t' t with h' | h'
        · exact Or.inl (Or.inr ⟨h', h2⟩)
        · exact Or.inr ⟨by omega, by rw [show t' = t by omega] at h2; exact h2⟩
    · have := mul_pred_add (a := 32 * sz + 22) (x := b - t) (by omega)
      rw [show b - t - 1 = b - (t + 1) by omega] at this
      rw [h45']
      omega
  · intro c₂ k₂ hI₂ hn₂ hk₂
    have h45 : c₂.nreg 45 = b := by have := hI₂.le; rw [hI₂.inp.r1] at hn₂; omega
    have htab₂ := hI₂.tab
    rw [h45] at htab₂
    refine ⟨?_, hI₂.frm, hI₂.inp, hI₂.r44, hI₂.r40, hI₂.r42, hI₂.mem, htab₂⟩
    beta_reduce at hk₂; config_simp at hk₂; simp only [Nat.sub_zero] at hk₂; omega

/-- A level: the three passes, then `sz := 2 sz`. -/
def levelP : Stmt := .seq pass1 (.seq pass2 (.seq pass3 (.instr (.addN 44 44 44))))

/-- The pairs below the level `sz`. -/
def BelowP (sz : ℕ) (s t : ℕ) : Prop := 2 ^ levOf s t < sz

/-- **A level.** -/
theorem levelP_exec (hL : LayP b Vb Db Fb Sb W) {H : ℝ} {sz T : ℕ} (hT : sz = 2 ^ T)
    (hszb : sz < b) (c : Config) (hc : WordsBounded W c) (hI : InP b Vb Db Fb Sb X D c)
    (h44 : c.nreg 44 = sz) (h40 : c.rreg 40 = H) (h42 : c.rreg 42 = 1)
    (htab : TabOK b Vb X D H (BelowP sz) c) :
    ∃ c' k, Exec P W levelP c c' k ∧ k ≤ (53 * b + 126) * b + 10 ∧
      (FrP b Vb Sb c c' ∧ InP b Vb Db Fb Sb X D c' ∧ c'.nreg 44 = sz + sz ∧ c'.rreg 40 = H ∧
        c'.rreg 42 = 1 ∧ TabOK b Vb X D H (BelowP (sz + sz)) c') := by
  have hw := hL.w; have hsd := hL.sd; have hdv := hL.dv
  have hsz : 0 < sz := by rw [hT]; exact Nat.two_pow_pos T
  unfold levelP
  refine spec_seq ?_
  refine spec_use (pass1_exec (P := P) hL hsz hszb.le c hc hI h44) ?_
  intro c₁ k₁ hk₁ hw₁ ⟨hF₁, hI₁, h44₁, hLG, hnm₁, hrm₁, hrr₁⟩
  refine spec_seq ?_
  refine spec_use (pass2_exec (P := P) hL hsz hszb.le c₁ hw₁ hI₁ h44₁
    (fun t ht => (hLG t ht).2)) ?_
  intro c₂ k₂ hk₂ hw₂ ⟨hF₂, hI₂, h44₂, hR₂, hnm₂, hrm₂, hrr₂⟩
  have hb₁ : ∀ a, Vb ≤ a → c₂.nmem a = c.nmem a := fun a ha => by
    rw [hnm₂ a (Or.inr (by omega)), hnm₁ a (Or.inr (by omega))]
  have hb₂ : c₂.rmem = c.rmem := by rw [hrm₂, hrm₁]
  have hrr : c₂.rreg = c.rreg := by rw [hrr₂, hrr₁]
  have htab₂ : TabOK b Vb X D H (BelowP sz) c₂ :=
    htab.of (fun a ha _ => hb₁ a ha) (fun a _ _ => by rw [hb₂])
  refine spec_seq ?_
  refine spec_use (pass3_exec (P := P) hL hT hszb.le c₂ hw₂ hI₂ h44₂ (by rw [hrr, h40])
    (by rw [hrr, h42]) hR₂ (fun t ht => by
      rw [hnm₂ _ (Or.inl (by omega))]; exact (hLG t ht).1) htab₂) ?_
  intro c₃ k₃ hk₃ hw₃ ⟨hF₃, hI₃, h44₃, h40₃, h42₃, _, htab₃⟩
  refine spec_instr (Exec.addN hw₃ 44 44 44 (by rw [h44₃]; omega)) fun _ => ?_
  have hF₄ : FrP b Vb Sb c₃ { c₃ with nreg := upd c₃.nreg 44 (c₃.nreg 44 + c₃.nreg 44) } :=
    ⟨fun r hr => by config_simp; rw [upd_other _ _ _ (by omega)], fun _ _ => rfl, fun _ _ => rfl,
      fun _ _ => rfl, rfl⟩
  have hmb : sz * b ≤ b * b := Nat.mul_le_mul_right b hszb.le
  have q1 : (7 * sz + 42) * b + (14 * sz + 62) * b + (32 * sz + 22) * b = 53 * (sz * b) + 126 * b :=
    by ring
  have q2 : (53 * b + 126) * b = 53 * (b * b) + 126 * b := by ring
  refine ⟨by omega, hF₁.trans (hF₂.trans (hF₃.trans hF₄)), hI₃.of hL hF₄,
    by config_simp; rw [h44₃], h40₃, h42₃, fun s t hs ht hst hp => ?_⟩
  refine htab₃ s t hs ht hst ?_
  unfold BelowP at hp
  by_cases hlt : 2 ^ levOf s t < sz
  · exact Or.inl hlt
  · right
    have e2 : sz + sz = 2 ^ (T + 1) := by rw [hT, pow_succ]; ring
    rw [e2] at hp
    rw [hT] at hlt
    have h1 := (Nat.pow_lt_pow_iff_right (by omega : 1 < 2)).1 hp
    have h2 : ¬ levOf s t < T := fun h => hlt ((Nat.pow_lt_pow_iff_right (by omega)).2 h)
    have hlev : 2 ^ levOf s t = sz := by rw [hT, show levOf s t = T by omega]
    obtain ⟨-, κ, hκ, hs'⟩ := lev_range hs ht hst
    rw [hlev] at hκ hs'
    exact ⟨ht, κ, hκ, hs'⟩

/-- The cost bound of a level. -/
def levelCostP (b : ℕ) : ℕ := (53 * b + 126) * b + 10

/-- The state of the level loop from `c₀`. -/
structure ILv (b Vb Db Fb Sb W : ℕ) (X : ℕ → ℕ → Prop) (D : ℕ → ℕ → ℤ) (H : ℝ)
    (c₀ c : Config) : Prop where
  wb : WordsBounded W c
  inp : InP b Vb Db Fb Sb X D c
  frm : FrP b Vb Sb c₀ c
  pow : ∃ T, c.nreg 44 = 2 ^ T
  r40 : c.rreg 40 = H
  r42 : c.rreg 42 = 1
  tab : TabOK b Vb X D H (BelowP (c.nreg 44)) c

/-- **The levels.** Started with `r44 = 1`, the loop writes the entries of all pairs `s ≠ t`. -/
theorem levelsP_exec (hL : LayP b Vb Db Fb Sb W) {H : ℝ} (c : Config) (hc : WordsBounded W c)
    (hI : InP b Vb Db Fb Sb X D c) (h44 : c.nreg 44 = 1) (h40 : c.rreg 40 = H)
    (h42 : c.rreg 42 = 1) :
    ∃ c' k, Exec P W (.whileLtN 44 1 levelP) c c' k ∧
      k ≤ (levelCostP b + 2) * (Nat.log 2 b + 1) + 2 ∧
      (FrP b Vb Sb c c' ∧ c'.rreg 40 = H ∧ c'.rreg 42 = 1 ∧
        TabOK b Vb X D H (fun _ _ => True) c') := by
  refine spec_while (ILv b Vb Db Fb Sb W X D H c)
    (fun c => (levelCostP b + 2) * (Nat.log 2 b + 1 - Nat.log 2 (c.nreg 44))) (fun c h => h.wb)
    ?_ ⟨hc, hI, FrP.refl _ _ _ _, ⟨0, by rw [h44]; rfl⟩, h40, h42,
      fun s t _ _ _ hp => by
        unfold BelowP at hp; rw [h44] at hp; have := Nat.two_pow_pos (levOf s t); omega⟩ ?_
  · intro c₁ hI₁ hlt
    rw [hI₁.inp.r1] at hlt
    obtain ⟨T, hT⟩ := hI₁.pow
    generalize hs : c₁.nreg 44 = sz at hT hlt
    have htab₁ := hI₁.tab
    rw [hs] at htab₁
    obtain ⟨c₂, k, hex, hk, hF, hI₂, h44', h40', h42', htab₂⟩ :=
      levelP_exec (P := P) hL hT hlt c₁ hI₁.wb hI₁.inp hs hI₁.r40 hI₁.r42 htab₁
    have hp : c₂.nreg 44 = 2 ^ (T + 1) := by rw [h44', hT, pow_succ]; ring
    refine ⟨c₂, k, hex, ⟨hex.wb_right, hI₂, hI₁.frm.trans hF, ⟨T + 1, hp⟩, h40', h42',
      by rw [h44']; exact htab₂⟩, ?_⟩
    have hs1 : 1 ≤ sz := by rw [hT]; exact Nat.one_le_two_pow
    have hl1 : Nat.log 2 (sz + sz) = Nat.log 2 sz + 1 := by
      rw [show sz + sz = sz * 2 by ring, Nat.log_mul_base (by norm_num) (by omega)]
    have hl2 : Nat.log 2 sz < Nat.log 2 b + 1 := by
      have := Nat.log_mono_right (b := 2) hlt.le; omega
    rw [h44', hl1]
    have := mul_pred_add (a := levelCostP b + 2) (x := Nat.log 2 b + 1 - Nat.log 2 sz)
      (by omega)
    rw [show Nat.log 2 b + 1 - Nat.log 2 sz - 1 = Nat.log 2 b + 1 - (Nat.log 2 sz + 1) by omega]
      at this
    unfold levelCostP at this ⊢
    omega
  · intro c₂ k₂ hI₂ hn₂ hk₂
    rw [hI₂.inp.r1] at hn₂
    refine ⟨?_, hI₂.frm, hI₂.r40, hI₂.r42, fun s t hs ht hst _ =>
      hI₂.tab s t hs ht hst (lt_of_lt_of_le (lev_range hs ht hst).1 (by omega))⟩
    rw [h44, show Nat.log 2 1 = 0 from Nat.log_one_right 2, Nat.sub_zero] at hk₂
    exact hk₂

/-- **The pass**: the bound `Hb b D`, then the levels. -/
def prepO : Stmt := .seq hProg (.seq (.instr (.constN 44 1)) (.whileLtN 44 1 levelP))

/-- The cost bound of `prepO`. -/
def prepCost (b : ℕ) : ℕ := (10 * b + 8) * b + 10 + 1 + ((levelCostP b + 2) * (Nat.log 2 b + 1) + 2)

/-- **The tables from the plain encoding.** From the flags `finB X s t` at `Fb + s b + t` and the
lengths `D s t` at `Db + s b + t` (`InP`), `prepO` writes `tVal b X D (Hb b D) s t`,
`tMul b X s t` (real memory) and `finB X s t` (natural memory) at `Vb + 2 (s b + t)` and
`Vb + 2 (s b + t) + 1` for all pairs `s ≠ t` of `0, …, b - 1`, within `prepCost b` steps; it
changes only the registers `44, …, 79` (natural) and `40, …, 46` (real), the natural memory in
`[Sb, Sb + 3b)` and the table region `[Vb, Vb + 2b²)`. -/
theorem prepO_exec (hL : LayP b Vb Db Fb Sb W) (c : Config) (hc : WordsBounded W c)
    (hI : InP b Vb Db Fb Sb X D c) :
    ∃ c' k, Exec P W prepO c c' k ∧ k ≤ prepCost b ∧
      (FrP b Vb Sb c c' ∧ TabOK b Vb X D (Hb b D) (fun _ _ => True) c') := by
  have hw := hL.w; have hsd := hL.sd; have hdv := hL.dv
  unfold prepO
  refine spec_seq ?_
  refine spec_use (hProg_exec (P := P) (D := D) (by omega) c hc hI.r1 hI.r41 hI.dv) ?_
  intro c₁ k₁ hk₁ hw₁ ⟨h40, h10, h42, _, hn, hr, hnm, hrm, ho⟩
  have hF₁ : FrP b Vb Sb c c₁ := ⟨fun r _ => by
      by_cases h : r = 10
      · rw [h, h10, hI.r10]
      · exact hn r h (by omega) (by omega) (by omega),
    fun r _ => hr r (by omega) (by omega) (by omega) (by omega), fun a _ => by rw [hnm],
    fun a _ => by rw [hrm], ho⟩
  have hI₁ := hI.of hL hF₁
  refine spec_seq ?_
  refine spec_instr (Exec.constN hw₁ 44 1 (by omega)) fun hw₂ => ?_
  have hF₂ : FrP b Vb Sb c₁ { c₁ with nreg := upd c₁.nreg 44 1 } :=
    ⟨fun r hr => by config_simp; rw [upd_other _ _ _ (by omega)], fun _ _ => rfl, fun _ _ => rfl,
      fun _ _ => rfl, rfl⟩
  refine spec_use (levelsP_exec (P := P) hL _ hw₂ (hI₁.of hL hF₂) (by config_simp) h40 h42) ?_
  intro c₃ k₃ hk₃ _ ⟨hF₃, _, _, htab⟩
  refine ⟨?_, hF₁.trans (hF₂.trans hF₃), htab⟩
  unfold prepCost; omega

end Monge

end PlanarFlow
