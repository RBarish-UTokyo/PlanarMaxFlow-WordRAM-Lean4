module

public import PlanarFlow.Monge.FRState

/-!
# FR-Dijkstra on the machine: settling a vertex

`settle` settles the vertex `x = r180` at the popped key `κ` (the real `r180`): its present
flag is cleared, its distance `κ + p x` is stored, it is marked settled, and the heap of the
vertices is repaired (`MSt.header`); then, if `x` is a corner, it is activated as a source in its
half block `sib (x / s)` of every level `s` (`lvl`, `MSt.level`); finally its explicit arcs are
relaxed (`arcBody`, `MSt.arc`).

* `bSum`: a sum over the half blocks; `potN`: the potential `Σ LD t · nst` of the activations
  (`PlanarFlow.Monge.FR.act_exec`).
* `settle_exec`: from the state `MSt` with the ghost run `(K, v, d)`, the state with the run
  extended by `x`, within `settleCost P x` steps plus the decrease of `potN`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace Monge

namespace FR

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs Heap

/-! ### The programs -/

/-- The header of the settling of `r180` at the key `rr180`: clear its present flag, store its
distance `κ + p x`, mark it settled, and the start of the repair of the heap of the vertices. -/
def hdr : Stmt :=
  block [.addN 187 109 180, .storeN 187 117, .addN 187 103 180, .loadR 181 187,
    .addR 181 180 181, .addN 187 108 180, .storeR 187 181, .addN 187 107 180, .storeN 187 110,
    .addN 170 100 180, .divN 170 170 111]

/-- **One level `s = r182` of the settling of `r180`**: activate `x` in its half block
`k = sib (x / s)` (if it exists), with the level bases `r181` (range minima), `r284`
(triplets), `r285` (leaves). -/
def lvl : Stmt :=
  .seq (block [.divN 183 180 182, .mulN 189 183 182, .subN 260 180 189, .modN 189 183 111]) <|
  .seq (.ifLtN 189 110 (.instr (.addN 183 183 110)) (.instr (.subN 183 183 110))) <|
  .seq (.instr (.mulN 187 183 182)) <|
  .seq (.ifLtN 187 101 (.seq (ctxW 245) (.seq tctx (.seq act bsync))) .skip) <|
  block [.addN 182 182 182, .addN 181 181 247, .addN 284 284 244, .addN 285 285 101]

/-- The levels of the settling of `r180`. -/
def lvls : Stmt :=
  .seq (block [.copyN 182 110, .copyN 181 246, .copyN 284 240, .constN 285 0])
    (.whileLtN 182 101 lvl)

/-- **Settle the vertex `r180` at the key `rr180`.** -/
def settle : Stmt :=
  .seq hdr <|
  .seq hpUp <|
  .seq (.ifLtN 180 101 lvls .skip) <|
  .seq (block [.addN 187 104 180, .loadN 185 187, .addN 187 187 110, .loadN 186 187]) <|
  .whileLtN 185 186 arcBody

/-! ### Sums over the half blocks -/

/-- A sum over the half blocks `(t, k)` (`2 ^ t < b`, `k 2 ^ t < b`). -/
noncomputable def bSum (P : Prm) (f : ℕ → ℕ → ℕ) : ℕ :=
  ∑ q ∈ Finset.range P.Lv ×ˢ Finset.range P.b,
    if 2 ^ q.1 < P.b ∧ q.2 * 2 ^ q.1 < P.b then f q.1 q.2 else 0

/-- **The potential of the activations**: `LD t` per start of every half block. -/
noncomputable def potN (P : Prm) (nm : ℕ → ℕ) : ℕ :=
  bSum P fun t k => LD t * nst (tbQ P t k) (2 ^ t) nm

variable {P : Prm} {I : Input}

lemma bSum_congr {f f' : ℕ → ℕ → ℕ}
    (h : ∀ t k, 2 ^ t < P.b → k * 2 ^ t < P.b → f' t k = f t k) : bSum P f' = bSum P f := by
  unfold bSum
  refine Finset.sum_congr rfl fun q _ => ?_
  split_ifs with hv
  · exact h q.1 q.2 hv.1 hv.2
  · rfl

/-- **Changing one half block** changes the sum by its change. -/
lemma bSum_step {f f' : ℕ → ℕ → ℕ} {t₀ k₀ : ℕ} (ht : 2 ^ t₀ < P.b) (hk : k₀ * 2 ^ t₀ < P.b)
    (h : ∀ t k, 2 ^ t < P.b → k * 2 ^ t < P.b → ¬ (t = t₀ ∧ k = k₀) → f' t k = f t k) :
    bSum P f' + f t₀ k₀ = bSum P f + f' t₀ k₀ := by
  have hq : (t₀, k₀) ∈ Finset.range P.Lv ×ˢ Finset.range P.b := by
    rw [Finset.mem_product, Finset.mem_range, Finset.mem_range]
    have := lt_Lv' ht
    have : 1 ≤ 2 ^ t₀ := Nat.one_le_two_pow
    refine ⟨by omega, ?_⟩
    have : k₀ ≤ k₀ * 2 ^ t₀ := Nat.le_mul_of_pos_right _ (by omega)
    omega
  unfold bSum
  rw [← Finset.add_sum_erase _ _ hq, ← Finset.add_sum_erase _ _ hq]
  have : ∑ q ∈ (Finset.range P.Lv ×ˢ Finset.range P.b).erase (t₀, k₀),
      (if 2 ^ q.1 < P.b ∧ q.2 * 2 ^ q.1 < P.b then f' q.1 q.2 else 0) =
      ∑ q ∈ (Finset.range P.Lv ×ˢ Finset.range P.b).erase (t₀, k₀),
      (if 2 ^ q.1 < P.b ∧ q.2 * 2 ^ q.1 < P.b then f q.1 q.2 else 0) := by
    refine Finset.sum_congr rfl fun q hq' => ?_
    have hne := Finset.ne_of_mem_erase hq'
    split_ifs with hv
    · exact h q.1 q.2 hv.1 hv.2 fun ⟨e1, e2⟩ => hne (Prod.ext e1 e2)
    · rfl
  rw [this, iteT ⟨ht, hk⟩, iteT ⟨ht, hk⟩]
  ring

/-- **A sum over the half blocks of at most `g t · 2 ^ t` each** is at most `2 b Σ g`. -/
theorem bSum_le {f : ℕ → ℕ → ℕ} {g : ℕ → ℕ}
    (h : ∀ t k, 2 ^ t < P.b → k * 2 ^ t < P.b → f t k ≤ g t * 2 ^ t) :
    bSum P f ≤ 2 * P.b * ∑ t ∈ Finset.range P.Lv, g t := by
  unfold bSum
  rw [Finset.sum_product, Finset.mul_sum]
  refine Finset.sum_le_sum fun t _ => ?_
  by_cases h2 : 2 ^ t < P.b
  · have hle : ∀ k ∈ Finset.range P.b,
        (if 2 ^ t < P.b ∧ k * 2 ^ t < P.b then f t k else 0) ≤
          if k * 2 ^ t < P.b then g t * 2 ^ t else 0 := by
      intro k _
      split_ifs with h1 h3
      · exact h t k h1.1 h1.2
      · exact absurd h1.2 h3
      · exact Nat.zero_le _
      · exact le_rfl
    refine (Finset.sum_le_sum hle).trans ?_
    rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul]
    have hsub : (Finset.range P.b).filter (fun k => k * 2 ^ t < P.b) ⊆
        Finset.range (P.b / 2 ^ t + 1) := by
      intro k hk
      rw [Finset.mem_filter] at hk
      rw [Finset.mem_range, Nat.lt_succ_iff, Nat.le_div_iff_mul_le (Nat.two_pow_pos t)]
      exact hk.2.le
    have hc := Finset.card_le_card hsub
    rw [Finset.card_range] at hc
    have h3 : (P.b / 2 ^ t + 1) * 2 ^ t ≤ 2 * P.b := by
      have := Nat.div_mul_le_self P.b (2 ^ t)
      rw [Nat.add_mul, Nat.one_mul]; omega
    have h4 : ((Finset.range P.b).filter (fun k => k * 2 ^ t < P.b)).card * 2 ^ t ≤ 2 * P.b :=
      (Nat.mul_le_mul_right _ hc).trans h3
    calc ((Finset.range P.b).filter (fun k => k * 2 ^ t < P.b)).card * (g t * 2 ^ t)
        = g t * (((Finset.range P.b).filter (fun k => k * 2 ^ t < P.b)).card * 2 ^ t) := by
          ring
      _ ≤ g t * (2 * P.b) := Nat.mul_le_mul_left _ h4
      _ = 2 * P.b * g t := by ring
  · have : ∀ k ∈ Finset.range P.b,
        (if 2 ^ t < P.b ∧ k * 2 ^ t < P.b then f t k else 0) = 0 := fun k _ => by
      rw [iteF (fun h => h2 h.1)]
    rw [Finset.sum_congr rfl this, Finset.sum_const_zero]; exact Nat.zero_le _

/-- A sum of zeros. -/
lemma bSum_zero {f : ℕ → ℕ → ℕ} (h : ∀ t k, 2 ^ t < P.b → k * 2 ^ t < P.b → f t k = 0) :
    bSum P f = 0 := by
  unfold bSum
  refine Finset.sum_eq_zero fun q _ => ?_
  split_ifs with hv
  · exact h q.1 q.2 hv.1 hv.2
  · rfl

/-- The potential of the activations depends only on the triplets. -/
lemma potN_congr {nm nm' : ℕ → ℕ}
    (h : ∀ t k, 2 ^ t < P.b → k * 2 ^ t < P.b → ∀ x < 2 ^ t,
      tPr (tbQ P t k) nm' x = tPr (tbQ P t k) nm x) : potN P nm' = potN P nm := by
  unfold potN
  refine bSum_congr fun t k ht hk => ?_
  unfold nst
  congr 2
  ext x
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, by rw [← h t k ht hk x h1]; exact h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, by rw [h t k ht hk x h1]; exact h2⟩

/-- **The potential after an operation on the triplets of one half block.** -/
lemma potN_step {nm nm' : ℕ → ℕ} {t₀ k₀ : ℕ} (ht : 2 ^ t₀ < P.b) (hk : k₀ * 2 ^ t₀ < P.b)
    (h : ∀ a, (a < tbQ P t₀ k₀ ∨ tbQ P t₀ k₀ + 16 * 2 ^ t₀ ≤ a) → a < P.bh → nm' a = nm a) :
    potN P nm' + LD t₀ * nst (tbQ P t₀ k₀) (2 ^ t₀) nm =
      potN P nm + LD t₀ * nst (tbQ P t₀ k₀) (2 ^ t₀) nm' := by
  unfold potN
  refine bSum_step (f := fun t k => LD t * nst (tbQ P t k) (2 ^ t) nm)
    (f' := fun t k => LD t * nst (tbQ P t k) (2 ^ t) nm') ht hk fun t k ht' hk' hb => ?_
  have hdisj := tbQ_disj ht' hk' ht hk hb
  have hQb' := tbQ_le_bh ht' hk'
  unfold nst
  congr 2
  ext x
  simp only [Finset.mem_filter, Finset.mem_range]
  have e : ∀ x < 2 ^ t, tPr (tbQ P t k) nm' x = tPr (tbQ P t k) nm x := fun x hx =>
    h _ (by omega) (by omega)
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, by rw [← e x h1]; exact h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, by rw [e x h1]; exact h2⟩

/-! ### The explicit arcs -/

/-- The state of the loop of the explicit arcs of `x`. -/
structure AI (P : Prm) (K : ℕ) (v : ℕ → ℕ) (d : ℕ → ℤ) (κ : ℝ) (X : ℕ → ℕ → ℕ → Prop)
    (x : ℕ) (c₀ c : Config) : Prop where
  wb : WordsBounded P.W c
  glob : Glob P c
  data : Data P c
  r180 : c.nreg 180 = x
  r186 : c.nreg 186 = P.off (x + 1)
  lo : P.off x ≤ c.nreg 185
  hi : c.nreg 185 ≤ P.off (x + 1)
  keepN : ∀ r, (r < 100 ∨ 200 ≤ r) → c.nreg r = c₀.nreg r
  keepR : ∀ r < 100, c.rreg r = c₀.rreg r
  out : c.output = c₀.output
  dx : dV P c.rmem x = κ + P.p x
  hiN : ∀ a, P.tb ≤ a → c.nmem a = c₀.nmem a
  si : MSt P K v d κ F2 F1 (arcEx x (c.nreg 185)) X c.nmem c.rmem

/-- **One explicit arc**: its reduced value from `x`, then `decKey`. -/
theorem arcBody_exec (hL : Lay P) (hF : Feas P) {K : ℕ} {v : ℕ → ℕ} {d : ℕ → ℤ} {κ : ℝ}
    {X : ℕ → ℕ → ℕ → Prop} {x i : ℕ} {c₀ : Config} (hx : x < P.N) (hi : i < K) (hvi : v i = x)
    (c : Config) (hI : AI P K v d κ X x c₀ c) (hlt : c.nreg 185 < c.nreg 186) :
    ∃ c' k', Exec I P.W arcBody c c' k' ∧ AI P K v d κ X x c₀ c' ∧
      (P.off (x + 1) - c'.nreg 185) * (decCost P.N + 15) + k' + 2 ≤
        (P.off (x + 1) - c.nreg 185) * (decCost P.N + 15) := by
  obtain ⟨hc, hG, hDa, h180, h186, hlo, hhi, hkN, hkR, hO, hdx, hiN, hS⟩ := hI
  have htb := tb_ge P
  have hw := lay_w hL
  have := hL.m2; have := hL.m3; have := hL.m4; have := hL.m5; have := hL.m6; have := hL.m1
  rw [h186] at hlt
  generalize he : c.nreg 185 = e at hlo hhi hlt hS
  have hm : e < P.m := by
    have := off_mono' hL (x + 1) P.N (by omega) le_rfl; rw [hL.off_last] at this; omega
  have hdst := dst_lt' hL hx hlt
  unfold arcBody
  refine spec_seq ?_
  exec_block
  · rw [hG.r104, hG.r100]; omega
  · config_simp; rw [hG.r104, hG.r100, hG.r110]; omega
  · config_simp; rw [hG.r104, hG.r100, hG.r110, he]; omega
  · config_simp; rw [hG.r108, h180]; omega
  · config_simp; rw [hG.r105, he]; omega
  · config_simp; rw [hG.r103, hG.r104, hG.r100, hG.r110, he]
    rw [show P.ob + P.N + 1 + e = P.ob + P.N + 1 + e from rfl, hDa.emem e hm]; omega
  generalize hc₁ : (Config.mk _ _ _ _ _ _ : Config) = c₁
  have hw₁ : WordsBounded P.W c₁ := hc₁ ▸ ‹_›
  have f175 : c₁.nreg 175 = P.dst e := by
    rw [← hc₁]; config_simp; rw [hG.r104, hG.r100, hG.r110, he]; exact hDa.emem e hm
  have r175 : c₁.rreg 175 = dV P c.rmem x + P.len e - P.p (P.dst e) := by
    rw [← hc₁]; config_simp
    rw [hG.r108, h180, hG.r105, he, hG.r103, hG.r104, hG.r100, hG.r110, hDa.emem e hm,
      hDa.lmem e hm, hDa.pmem _ hdst]
    unfold dV; rw [Nat.add_comm P.db x]
  have fK : ∀ r, r ≠ 175 → r ≠ 187 → c₁.nreg r = c.nreg r := fun r h1 h2 => by
    rw [← hc₁]; config_simp; upd_tac
  have fR : ∀ r, r ≠ 175 → r ≠ 180 → c₁.rreg r = c.rreg r := fun r h1 h2 => by
    rw [← hc₁]; config_simp; upd_tac
  have fN : c₁.nmem = c.nmem := by rw [← hc₁]
  have fM : c₁.rmem = c.rmem := by rw [← hc₁]
  have fO : c₁.output = c.output := by rw [← hc₁]
  have hG₁ : Glob P c₁ := hG.of fun r h1 h2 => fK r (by omega) (by omega)
  refine spec_seq ?_
  refine spec_use (decKey_exec (I := I) hL c₁ hw₁ hG₁ (by rw [f175]; exact hdst)
    (by rw [fN]; exact hS.hp.pr_le) (by rw [f175, fN]; exact hS.hp.sf_le _ hdst)
    (by rw [fN, fM]; exact hS.hp.win)) ?_
  intro c₂ k₂ hk₂ hw₂ ⟨hp₂, hk2, hW₂, hK₂, hR₂, hO₂, hN₂, hM₂⟩
  rw [f175, r175, fN, fM] at hp₂ hk2
  rw [f175] at hN₂ hM₂
  rw [fN] at hN₂; rw [fM] at hM₂
  have hD := decEff_of_dec hp₂ hk2 hW₂ (fun a ha => hN₂ a (by omega) (by omega))
    (fun a ha => hM₂ a (by omega))
  refine spec_instr (Exec.addN hw₂ 185 185 110 (by
    rw [hK₂ 185 (by omega), fK 185 (by omega) (by omega), he, hK₂ 110 (by omega), hG₁.r110]
    have := hL.m3; omega)) fun hw₃ => ?_
  have k185 : c₂.nreg 185 = e := by rw [hK₂ 185 (by omega), fK 185 (by omega) (by omega), he]
  have k110 : c₂.nreg 110 = 1 := by rw [hK₂ 110 (by omega), hG₁.r110]
  have hS₂ := hS.arc hL hF hD hx hi hvi hlo hlt hdx
  refine ⟨⟨hw₃, hG.of fun r h1 h2 => ?_, hDa.of hL (fun a ha => ?_) (fun a ha => ?_), ?_, ?_,
    ?_, ?_, fun r hr => ?_, fun r hr => ?_, ?_, ?_, fun a ha => ?_, ?_⟩, ?_⟩
  · config_simp; rw [upd_other _ _ _ (by omega), hK₂ r (by omega), fK r (by omega) (by omega)]
  · config_simp; rw [hN₂ a (by omega) (by omega)]
  · config_simp; rw [hM₂ a (by omega)]
  · config_simp; rw [hK₂ 180 (by omega), fK 180 (by omega) (by omega), h180]
  · config_simp; rw [hK₂ 186 (by omega), fK 186 (by omega) (by omega), h186]
  · config_simp; rw [k185, k110]; omega
  · config_simp; rw [k185, k110]; omega
  · config_simp; rw [upd_other _ _ _ (by omega), hK₂ r (by omega), fK r (by omega) (by omega)]
    exact hkN r hr
  · config_simp; rw [hR₂ r (by omega), fR r (by omega) (by omega)]; exact hkR r hr
  · config_simp; rw [hO₂, fO, hO]
  · config_simp; rw [hD.dist hL hx]; exact hdx
  · config_simp; rw [hN₂ a (by omega) (by omega)]; exact hiN a ha
  · config_simp; rw [k185, k110]; exact hS₂
  · config_simp; rw [k185, k110]
    have : P.off (x + 1) - e = (P.off (x + 1) - (e + 1)) + 1 := by omega
    rw [this, Nat.add_mul, Nat.one_mul]
    omega

/-- **The explicit arcs of `x`**: read their range, then relax each one. -/
theorem arcs_exec (hL : Lay P) (hF : Feas P) {K : ℕ} {v : ℕ → ℕ} {d : ℕ → ℤ} {κ : ℝ}
    {X : ℕ → ℕ → ℕ → Prop} {x i : ℕ} (hx : x < P.N) (hi : i < K) (hvi : v i = x)
    (c : Config) (hc : WordsBounded P.W c) (hG : Glob P c) (hDa : Data P c)
    (h180 : c.nreg 180 = x) (hdx : dV P c.rmem x = κ + P.p x)
    (hS : MSt P K v d κ F2 F1 (arcEx x (P.off x)) X c.nmem c.rmem) :
    ∃ c' k', Exec I P.W (.seq (block [.addN 187 104 180, .loadN 185 187, .addN 187 187 110,
      .loadN 186 187]) (.whileLtN 185 186 arcBody)) c c' k' ∧
      k' ≤ (P.off (x + 1) - P.off x) * (decCost P.N + 15) + 6 ∧
      Glob P c' ∧ Data P c' ∧ (∀ r, (r < 100 ∨ 200 ≤ r) → c'.nreg r = c.nreg r) ∧
      (∀ r < 100, c'.rreg r = c.rreg r) ∧ c'.output = c.output ∧
      (∀ a, P.tb ≤ a → c'.nmem a = c.nmem a) ∧ MSt P K v d κ F2 F1 F2 X c'.nmem c'.rmem := by
  have htb := tb_ge P
  have hw := lay_w hL
  have := hL.m2; have := hL.m3; have := hL.m4; have := hL.m5; have := hL.m6
  have hmono := off_mono' hL x (x + 1) (by omega) (by omega)
  refine spec_seq ?_
  exec_block
  · rw [hG.r104, h180]; omega
  · config_simp; rw [hG.r104, h180, hG.r110]; omega
  generalize hc₁ : (Config.mk _ _ _ _ _ _ : Config) = c₁
  have hw₁ : WordsBounded P.W c₁ := hc₁ ▸ ‹_›
  have f185 : c₁.nreg 185 = P.off x := by
    rw [← hc₁]; config_simp; rw [hG.r104, h180]; exact hDa.omem x hx.le
  have f186 : c₁.nreg 186 = P.off (x + 1) := by
    rw [← hc₁]; config_simp; rw [hG.r104, h180, hG.r110, Nat.add_assoc]
    exact hDa.omem (x + 1) hx
  have fK : ∀ r, r ≠ 185 → r ≠ 186 → r ≠ 187 → c₁.nreg r = c.nreg r := fun r h1 h2 h3 => by
    rw [← hc₁]; config_simp; upd_tac
  have fN : c₁.nmem = c.nmem := by rw [← hc₁]
  have fM : c₁.rmem = c.rmem := by rw [← hc₁]
  have fR : c₁.rreg = c.rreg := by rw [← hc₁]
  have fO : c₁.output = c.output := by rw [← hc₁]
  have hI₁ : AI P K v d κ X x c c₁ :=
    ⟨hw₁, hG.of fun r h1 h2 => fK r (by omega) (by omega) (by omega),
      hDa.of hL (fun _ _ => by rw [fN]) (fun _ _ => by rw [fM]),
      by rw [fK 180 (by omega) (by omega) (by omega), h180], f186, by rw [f185],
      by rw [f185]; exact hmono, fun r hr => fK r (by omega) (by omega) (by omega),
      fun r _ => by rw [fR], fO, by rw [fM]; exact hdx, fun a _ => by rw [fN],
      by rw [f185, fN, fM]; exact hS⟩
  refine spec_while (AI P K v d κ X x c)
    (fun c' => (P.off (x + 1) - c'.nreg 185) * (decCost P.N + 15)) (fun _ h => h.wb)
    (fun c' hI hlt => arcBody_exec hL hF hx hi hvi c' hI hlt) hI₁ ?_
  intro c₂ k₂ hI₂ hn₂ hk₂
  rw [f185] at hk₂
  have h185 : c₂.nreg 185 = P.off (x + 1) := by have := hI₂.hi; rw [hI₂.r186] at hn₂; omega
  refine ⟨by omega, hI₂.glob, hI₂.data, hI₂.keepN, hI₂.keepR, hI₂.out, hI₂.hiN, ?_⟩
  have := hI₂.si; rw [h185] at this
  refine ⟨this.hp, this.gh, fun u hu hsu e h1 h2 hse => ?_, this.kmin, this.blk, this.bh⟩
  rcases this.arcs u hu hsu e h1 h2 hse with ⟨rfl, h3⟩ | h'
  · omega
  · exact Or.inr h'

/-! ### The levels -/

/-- The cost of one level of the settling, besides the potential. -/
def lvC (P : Prm) : ℕ := actCost P.Lv + 49 * P.TB + 80

lemma actCost_mono {t t' : ℕ} (h : t ≤ t') : actCost t ≤ actCost t' := by
  unfold actCost rmqCost; omega

/-- The state of the loop of the levels of the settling of `x`, before the level `t₀`. -/
structure LI (P : Prm) (K : ℕ) (v : ℕ → ℕ) (d : ℕ → ℤ) (κ : ℝ) (X : ℕ → ℕ → ℕ → Prop)
    (x : ℕ) (c₀ : Config) (t₀ : ℕ) (c : Config) : Prop where
  wb : WordsBounded P.W c
  glob : Glob P c
  gx : GX P c
  data : Data P c
  r180 : c.nreg 180 = x
  r182 : c.nreg 182 = 2 ^ t₀
  r181 : c.nreg 181 = P.rb + 8 * P.b * P.Lv * t₀
  r284 : c.nreg 284 = P.tb + 32 * P.b * t₀
  r285 : c.nreg 285 = t₀ * P.b
  tle : t₀ ≤ P.Lv
  keepN : ∀ r < 100, c.nreg r = c₀.nreg r
  keepR : ∀ r < 100, c.rreg r = c₀.rreg r
  out : c.output = c₀.output
  sx : sfV P c.nmem x = 1
  dx : dV P c.rmem x = κ + P.p x
  si : MSt P K v d κ (pend x t₀) F1 (arcEx x (P.off x)) X c.nmem c.rmem

/-- **One level of the settling of `x`.** -/
theorem lvl_exec (hL : Lay P) (hDc : Crossing P.b P.D) (hF : Feas P) {K : ℕ} {v : ℕ → ℕ}
    {d : ℕ → ℤ} {κ : ℝ} {X : ℕ → ℕ → ℕ → Prop} {x t₀ : ℕ} {c₀ : Config} (hx : x < P.b)
    (c : Config) (hI : LI P K v d κ X x c₀ t₀ c) (hlt : c.nreg 182 < c.nreg 101) :
    ∃ c' k', Exec I P.W lvl c c' k' ∧ LI P K v d κ X x c₀ (t₀ + 1) c' ∧
      potN P c'.nmem + (P.Lv - (t₀ + 1)) * lvC P + k' + 2 ≤
        potN P c.nmem + (P.Lv - t₀) * lvC P := by
  obtain ⟨hc, hG, hX, hDa, h180, h182, h181, h284, h285, htle, hkN, hkR, hO, hsx, hdx, hS⟩ := hI
  rw [h182, hG.r101] at hlt
  have ht := hlt
  have hLv := lt_Lv' ht
  have hs1 : 1 ≤ 2 ^ t₀ := Nat.one_le_two_pow
  have hw := hL.wx
  have hw0 := hL.w
  have hbN := hL.bN
  have hbTB := lt_two_pow_TB P
  have hbw := bh_le_W hL
  have hdvx : x / 2 ^ t₀ * 2 ^ t₀ ≤ x := Nat.div_mul_le_self x _
  have hdx' : x / 2 ^ t₀ ≤ x := Nat.div_le_self x _
  have hlt2 := Nat.lt_div_mul_add (a := x) (b := 2 ^ t₀) (by omega)
  have hsib : sib (x / 2 ^ t₀) * 2 ^ t₀ ≤ x + 2 ^ t₀ := by
    have := Nat.mul_le_mul_right (2 ^ t₀) (sib_le (x / 2 ^ t₀))
    rw [Nat.add_mul, Nat.one_mul] at this; omega
  unfold lvl
  refine spec_seq ?_
  exec_block
  · config_simp; rw [h180, h182]; omega
  generalize hc₁ : (Config.mk _ _ _ _ _ _ : Config) = c₁
  have hw₁ : WordsBounded P.W c₁ := hc₁ ▸ ‹_›
  have f183 : c₁.nreg 183 = x / 2 ^ t₀ := by rw [← hc₁]; config_simp; rw [h180, h182]
  have f189 : c₁.nreg 189 = x / 2 ^ t₀ % 2 := by
    rw [← hc₁]; config_simp; rw [h180, h182, hG.r111]
  have f260 : c₁.nreg 260 = x - x / 2 ^ t₀ * 2 ^ t₀ := by
    rw [← hc₁]; config_simp; rw [h180, h182]
  have fK : ∀ r, r ≠ 183 → r ≠ 189 → r ≠ 260 → c₁.nreg r = c.nreg r := fun r h1 h2 h3 => by
    rw [← hc₁]; config_simp; upd_tac
  have fN : c₁.nmem = c.nmem := by rw [← hc₁]
  have fM : c₁.rmem = c.rmem := by rw [← hc₁]
  have fR : c₁.rreg = c.rreg := by rw [← hc₁]
  have fO : c₁.output = c.output := by rw [← hc₁]
  have k110 : c₁.nreg 110 = 1 := (fK 110 (by omega) (by omega) (by omega)).trans hG.r110
  refine spec_seq ?_
  obtain ⟨c₂, k₂, e₂, hk₂, g183, gK, gR, gN, gM, gO⟩ : ∃ c₂ k₂, Exec I P.W
      (.ifLtN 189 110 (.instr (.addN 183 183 110)) (.instr (.subN 183 183 110))) c₁ c₂ k₂ ∧
      k₂ ≤ 3 ∧ c₂.nreg 183 = sib (x / 2 ^ t₀) ∧ (∀ r, r ≠ 183 → c₂.nreg r = c₁.nreg r) ∧
      c₂.rreg = c₁.rreg ∧ c₂.nmem = c₁.nmem ∧ c₂.rmem = c₁.rmem ∧ c₂.output = c₁.output := by
    by_cases hp : x / 2 ^ t₀ % 2 = 0
    · refine spec_ifLtN_true (by rw [f189, k110]; omega) ?_
      refine spec_instr (Exec.addN hw₁ 183 183 110 (by rw [f183, k110]; omega)) fun _ =>
        ⟨by omega, ?_, fun r hr => by config_simp; upd_tac, rfl, rfl, rfl, rfl⟩
      config_simp; rw [f183, k110]; unfold sib; simp [hp]
    · refine spec_ifLtN_false (by rw [f189, k110]; omega) ?_
      refine spec_instr (Exec.subN hw₁ 183 183 110) fun _ =>
        ⟨by omega, ?_, fun r hr => by config_simp; upd_tac, rfl, rfl, rfl, rfl⟩
      config_simp; rw [f183, k110]; unfold sib; simp [hp]
  refine ⟨c₂, k₂, e₂, ?_⟩
  have hw₂ := e₂.wb_right
  have l182 : c₂.nreg 182 = 2 ^ t₀ := by
    rw [gK 182 (by omega), fK 182 (by omega) (by omega) (by omega), h182]
  refine spec_seq ?_
  refine spec_instr (Exec.mulN hw₂ 187 183 182 (by rw [g183, l182]; omega)) fun hw₃ => ?_
  generalize hc₃ : (Config.mk _ _ _ _ _ _ : Config) = c₃ at hw₃ ⊢
  have f187 : c₃.nreg 187 = sib (x / 2 ^ t₀) * 2 ^ t₀ := by
    rw [← hc₃]; config_simp; rw [g183, l182]
  have k3 : ∀ r, r ≠ 183 → r ≠ 187 → r ≠ 189 → r ≠ 260 → c₃.nreg r = c.nreg r :=
    fun r h1 h2 h3 h4 => by
      rw [← hc₃]; config_simp; rw [upd_other _ _ _ h2, gK r h1, fK r h1 h3 h4]
  have e3N : c₃.nmem = c.nmem := by rw [← hc₃]; config_simp; rw [gN, fN]
  have e3M : c₃.rmem = c.rmem := by rw [← hc₃]; config_simp; rw [gM, fM]
  have e3R : c₃.rreg = c.rreg := by rw [← hc₃]; config_simp; rw [gR, fR]
  have e3O : c₃.output = c.output := by rw [← hc₃]; config_simp; rw [gO, fO]
  have g3 : c₃.nreg 183 = sib (x / 2 ^ t₀) := by rw [← hc₃]; config_simp; exact g183
  have g3' : c₃.nreg 260 = x - x / 2 ^ t₀ * 2 ^ t₀ := by
    rw [← hc₃]; config_simp; rw [gK 260 (by omega)]; exact f260
  have hG₃ : Glob P c₃ := hG.of fun r h1 h2 => k3 r (by omega) (by omega) (by omega) (by omega)
  have hX₃ : GX P c₃ := hX.of fun r h1 h2 => k3 r (by omega) (by omega) (by omega) (by omega)
  have hDa₃ : Data P c₃ := hDa.of hL (fun a _ => by rw [e3N]) (fun a _ => by rw [e3M])
  have hLvb : P.Lv * P.b < 2 ^ P.TB := by have := lt_two_pow_TB P; rw [Nat.mul_comm]; exact this
  have hlvb : (t₀ + 1) * P.b ≤ P.Lv * P.b := Nat.mul_le_mul_right _ hLv
  have hl8 : 8 * P.b * P.Lv * (t₀ + 1) ≤ 8 * P.b * P.Lv * P.Lv := Nat.mul_le_mul_left _ hLv
  have hl32 : 32 * P.b * (t₀ + 1) ≤ 32 * P.b * P.Lv := Nat.mul_le_mul_left _ hLv
  have hbhW : P.bh ≤ P.W := by unfold Prm.rb at hw; omega
  have hbhe : P.bh = P.tb + 32 * P.b * P.Lv := rfl
  have h8e : 8 * P.b * P.Lv * (t₀ + 1) = 8 * P.b * P.Lv * t₀ + 8 * P.b * P.Lv := by ring
  have h32e : 32 * P.b * (t₀ + 1) = 32 * P.b * t₀ + 32 * P.b := by ring
  have hbe' : (t₀ + 1) * P.b = t₀ * P.b + P.b := by ring
  have hTBW : 2 ^ P.TB ≤ P.W := by omega
  -- the branch: the activation in the half block, or nothing
  suffices hbr : ∃ c₄ k₄, Exec I P.W
      (.ifLtN 187 101 (.seq (ctxW 245) (.seq tctx (.seq act bsync))) .skip) c₃ c₄ k₄ ∧
      Glob P c₄ ∧ GX P c₄ ∧ Data P c₄ ∧ c₄.nreg 180 = x ∧ c₄.nreg 182 = 2 ^ t₀ ∧
      c₄.nreg 181 = P.rb + 8 * P.b * P.Lv * t₀ ∧ c₄.nreg 284 = P.tb + 32 * P.b * t₀ ∧
      c₄.nreg 285 = t₀ * P.b ∧ (∀ r < 100, c₄.nreg r = c.nreg r) ∧
      (∀ r < 100, c₄.rreg r = c.rreg r) ∧ c₄.output = c.output ∧ sfV P c₄.nmem x = 1 ∧
      dV P c₄.rmem x = κ + P.p x ∧
      MSt P K v d κ (pend x (t₀ + 1)) F1 (arcEx x (P.off x)) X c₄.nmem c₄.rmem ∧
      potN P c₄.nmem + k₄ + 14 ≤ potN P c.nmem + lvC P by
    obtain ⟨c₄, k₄, e₄, hG₄, hX₄, hDa₄, a180, a182, a181, a284, a285, aN, aR, aO, a1, a2, hS₄,
      hpot⟩ := hbr
    have hw₄ := e₄.wb_right
    refine spec_seq ⟨c₄, k₄, e₄, ?_⟩
    exec_block
    · rw [a182]; omega
    · config_simp; rw [a181, hX₄.r247]; omega
    · config_simp; rw [a284, hX₄.r244]; omega
    · config_simp; rw [a285, hG₄.r101]; omega
    refine ⟨⟨‹_›, hG₄.of fun r h1 h2 => by config_simp; upd_tac,
      hX₄.of fun r h1 h2 => by config_simp; upd_tac,
      hDa₄.of hL (fun _ _ => rfl) (fun _ _ => rfl), ?_, ?_, ?_, ?_, ?_, by omega,
      fun r hr => ?_, fun r hr => ?_, ?_, a1, a2, hS₄⟩, ?_⟩
    · config_simp; exact a180
    · config_simp; rw [a182, pow_succ]; ring
    · config_simp; rw [a181, hX₄.r247]; ring
    · config_simp; rw [a284, hX₄.r244]; ring
    · config_simp; rw [a285, hG₄.r101]; ring
    · config_simp; rw [upd_other _ _ _ (by omega), upd_other _ _ _ (by omega),
        upd_other _ _ _ (by omega), upd_other _ _ _ (by omega), aN r hr, hkN r hr]
    · config_simp; rw [aR r hr, hkR r hr]
    · config_simp; rw [aO, hO]
    · config_simp
      have : P.Lv - t₀ = P.Lv - (t₀ + 1) + 1 := by omega
      rw [this, Nat.add_mul, Nat.one_mul]
      omega
  by_cases hk : sib (x / 2 ^ t₀) * 2 ^ t₀ < P.b
  · generalize hk₀ : sib (x / 2 ^ t₀) = k₀ at hk g3 f187
    have hsk : sib k₀ = x / 2 ^ t₀ := by rw [← hk₀, sib_sib]
    have hnc0 : hbNc P.b (2 ^ t₀) k₀ ≤ 2 ^ t₀ := hbNc_le
    have hσx : x - x / 2 ^ t₀ * 2 ^ t₀ < hbNc P.b (2 ^ t₀) k₀ := by
      unfold hbNc; rw [hsk]; omega
    have hsrc : sib k₀ * 2 ^ t₀ + (x - x / 2 ^ t₀ * 2 ^ t₀) = x := by rw [hsk]; omega
    have hB := hS.blk t₀ k₀ ht hk
    refine spec_ifLtN_true (by rw [f187, hG₃.r101]; exact hk) ?_
    refine spec_seq ?_
    refine spec_use (ctxW_exec (I := I) (s := 2 ^ t₀) (k := k₀) (LB := P.rb + 8 * P.b * P.Lv * t₀)
      (m := 4 * P.Lv) hL c₃ hw₃ hG₃
      (by rw [k3 182 (by omega) (by omega) (by omega) (by omega)]; exact h182) g3
      (by rw [k3 181 (by omega) (by omega) (by omega) (by omega)]; exact h181) hX₃.r245
      (by omega) (by omega) hk hs1 ht.le
      (by have := rbB_le_W hL ht hk; unfold rbB at this; omega)) ?_
    intro c₄ k₄ hk₄ hw₄ ⟨hH₄, h189₄, hK₄, hR₄, hN₄, hM₄, hO₄⟩
    have k4 : ∀ r, (r < 120 ∨ 126 ≤ r) → r ≠ 189 → r ≠ 183 → r ≠ 187 → r ≠ 260 →
        c₄.nreg r = c.nreg r := fun r h1 h2 h3 h4 h5 => by
      rw [hK₄ r h1 h2]; exact k3 r h3 h4 h2 h5
    have hG₄ : Glob P c₄ := hG.of fun r h1 h2 => k4 r (by omega) (by omega) (by omega) (by omega)
      (by omega)
    refine spec_seq ?_
    refine spec_use (tctx_exec (I := I) (TB := P.tb + 32 * P.b * t₀) c₄ hw₄ hG₄ hH₄
      (by rw [k4 284 (by omega) (by omega) (by omega) (by omega) (by omega)]; exact h284)
      (by have := tbQ_le_bh ht hk; unfold tbQ at this; omega)) ?_
    intro c₅ k₅ hk₅ hw₅ ⟨hT₅, hF₅, hN₅, hM₅⟩
    have k5 : ∀ r, r ≠ 208 → r ≠ 209 → c₅.nreg r = c₄.nreg r := fun r h1 h2 => hF₅.n r (by omega)
    have e5N : c₅.nmem = c.nmem := by rw [hN₅, hN₄, e3N]
    have e5M : c₅.rmem = c.rmem := by rw [hM₅, hM₄, e3M]
    have hG₅ : Glob P c₅ := hG₄.of fun r h1 h2 => k5 r (by omega) (by omega)
    have hX₅ : GX P c₅ := hX.of fun r h1 h2 => by
      rw [k5 r (by omega) (by omega)]; exact k4 r (by omega) (by omega) (by omega) (by omega)
        (by omega)
    have hDa₅ : Data P c₅ := hDa.of hL (fun a _ => by rw [e5N]) (fun a _ => by rw [e5M])
    have hH₅ : HCtx P (rbB P t₀ k₀) (2 ^ t₀) k₀ c₅ := hH₄.of fun r h1 h2 => k5 r (by omega)
      (by omega)
    have hT₅' : TCtx (tbQ P t₀ k₀) (2 ^ t₀) c₅ := by unfold tbQ; exact hT₅
    -- the entries of the half block
    have hA : AntiM (hbNr P.b (2 ^ t₀) k₀) (hbNc P.b (2 ^ t₀) k₀)
        (fun ρ σ => hbe P c₅.rmem t₀ k₀ σ + hbF P.b P.D P.p (2 ^ t₀) k₀ ρ σ) := by
      have h := (antiM_hbF hDc P.p hk).add_col (hbe P c₅.rmem t₀ k₀)
      exact fun ρ ρ' σ σ' h1 h2 h3 h4 => h ρ ρ' σ σ' h1 (lt_of_lt_of_le h2 (Nat.min_le_left _ _))
        h3 h4
    have hna : ¬ hbAct P (pend x t₀) c₅.nmem t₀ k₀ (x - x / 2 ^ t₀ * 2 ^ t₀) := fun h =>
      h.2.2 ⟨hsrc, le_rfl⟩
    have hκ : ∀ ρ < hbNr P.b (2 ^ t₀) k₀, κ ≤ hbe P c₅.rmem t₀ k₀ (x - x / 2 ^ t₀ * 2 ^ t₀) +
        hbF P.b P.D P.p (2 ^ t₀) k₀ ρ (x - x / 2 ^ t₀ * 2 ^ t₀) := by
      intro ρ hρ
      have hρs : ρ < 2 ^ t₀ := lt_of_lt_of_le hρ (Nat.min_le_left _ _)
      have hyb : k₀ * 2 ^ t₀ + ρ < P.b := by unfold hbNr at hρ; omega
      have hne : x ≠ k₀ * 2 ^ t₀ + ρ := by
        rw [← hsrc]; exact src_ne_tgt (by omega) hρs
      have hfe := hF x (k₀ * 2 ^ t₀ + ρ) (P.D x (k₀ * 2 ^ t₀ + ρ)) (Or.inl ⟨hx, hyb, hne, rfl⟩)
      unfold hbe; rw [hsrc, e5M, hdx, hbF_live hyb, hsrc]
      have : ((P.p (k₀ * 2 ^ t₀ + ρ) : ℤ) : ℝ) ≤ P.p x + P.D x (k₀ * 2 ^ t₀ + ρ) := by
        exact_mod_cast hfe
      push_cast; linarith
    obtain ⟨own, hrep⟩ := hB.rep
    rw [← e5N, ← e5M] at hrep
    obtain ⟨c₆, k₆, e₆, hk₆, hf₆, ⟨own', hT₆, hown'⟩, hp₆, hkey₆, hW₆, hWl₆, hn₆, hr₆, hF₆⟩ :=
      blkStep_exec hL (I := I) (κ := κ) ht hk c₅ hw₅ ⟨hG₅, hH₅, hDa₅⟩
        hT₅' hX₅ (by rw [k5 260 (by omega) (by omega), hK₄ 260 (by omega) (by omega)]; exact g3')
        (by rw [k5 285 (by omega) (by omega),
          k4 285 (by omega) (by omega) (by omega) (by omega) (by omega)]; exact h285)
        (by rw [k5 183 (by omega) (by omega), hK₄ 183 (by omega) (by omega)]; exact g3)
        (by rw [e5N]; exact hB.ready (by omega))
        (fun σ _ => rfl) hA hna hσx hκ (hrep.imp id fun h => ⟨h.1, h.2.1⟩)
        (fun y hy => by rw [e5N]; exact hS.bh.pr y hy) (by rw [e5N, e5M]; exact hS.bh.win)
        (by rw [e5N]; exact hS.bh.wl)
    refine ⟨c₆, k₆, e₆, ?_⟩
    have hQb := tbQ_le_bh ht hk
    have hQt : P.tb ≤ tbQ P t₀ k₀ := tb_le_tbQ
    have htb := tb_ge P
    have hlo6 : ∀ a < P.hb, c₆.nmem a = c₅.nmem a := fun a ha =>
      hn₆ a (Or.inl (by unfold Prm.hb at ha; omega)) (Or.inl (by unfold Prm.hb at ha; omega))
    have hlo6r : ∀ a < P.hb, c₆.rmem a = c₅.rmem a := fun a ha =>
      hr₆ a (Or.inl (by unfold Prm.hb at ha; omega)) (by unfold Prm.hb at ha; omega)
    have hhb : P.hb = P.wb + 3 * P.N := rfl
    have := lay_low hL
    have k6 : ∀ r, ¬ (AcN r ∨ BSn r) → c₆.nreg r = c₅.nreg r := hF₆.n
    have kk : ∀ r, (r < 120 ∨ (139 ≤ r ∧ r < 183) ∨ (240 ≤ r ∧ r < 248) ∨ r = 284 ∨
        r = 285) → c₆.nreg r = c.nreg r := fun r hr => by
      rw [k6 r (by simp only [AcN, BSn, TPn]; omega), k5 r (by omega) (by omega)]
      exact k4 r (by omega) (by omega) (by omega) (by omega) (by omega)
    have hS₅ : MSt P K v d κ (pend x t₀) F1 (arcEx x (P.off x)) X c₅.nmem c₅.rmem := by
      rw [e5N, e5M]; exact hS
    have hκ' : ∀ ρ < hbNr P.b (2 ^ t₀) k₀, ¬ X t₀ k₀ ρ →
        κ ≤ hbe P c₅.rmem t₀ k₀ (own' ρ) + hbF P.b P.D P.p (2 ^ t₀) k₀ ρ (own' ρ) := by
      intro ρ hρ hXρ
      rcases hT₆.heap.ok.act ρ hρ with hact | ha'
      · rcases hown' ρ with h | h
        · rw [h]; exact hκ ρ hρ
        · rcases hrep with ⟨-, hno, -⟩ | ⟨-, -, hk'⟩
          · exact absurd hact (hno _)
          · rw [h]; exact hk' ρ hρ hXρ
      · rw [ha']; exact hκ ρ hρ
    have hsx₅ : sfV P c₅.nmem x = 1 := by rw [e5N]; exact hsx
    have hpot := potN_step (nm := c₅.nmem) (nm' := c₆.nmem) ht hk fun a h1 h2 =>
      hn₆ a h1 (Or.inl h2)
    subst hk₀
    have hS₆ := hS₅.level hL hx hsx₅ ht hk hf₆ ⟨own', hT₆, hκ'⟩ hp₆ hkey₆ hW₆ hWl₆ hn₆ hr₆
    refine ⟨hG.of fun r h1 h2 => kk r (by omega), hX.of fun r h1 h2 => kk r (by omega),
      hDa.of hL (fun a ha => by rw [hlo6 a (by omega), e5N]) (fun a ha => by
        rw [hlo6r a (by omega), e5M]), by rw [kk 180 (by omega)]; exact h180,
      by rw [kk 182 (by omega)]; exact h182, by rw [kk 181 (by omega)]; exact h181,
      by rw [kk 284 (by omega)]; exact h284, by rw [kk 285 (by omega)]; exact h285,
      fun r hr => kk r (by omega), fun r hr => ?_, by rw [hF₆.o, hF₅.o, hO₄, e3O],
      by unfold sfV; rw [hlo6 _ (by omega), e5N]; exact hsx,
      by unfold dV; rw [hlo6r _ (by omega), e5M]; exact hdx, hS₆, ?_⟩
    · rw [hF₆.r r (by simp only [AcR, TPr]; omega), hF₅.r r id, hR₄, e3R]
    · have hm := actCost_mono (show t₀ ≤ P.Lv by omega)
      rw [← e5N]
      unfold lvC
      omega
  · refine spec_ifLtN_false (by rw [f187, hG₃.r101]; exact hk) ?_
    refine spec_skip hw₃ ⟨hG₃, hX₃, hDa₃, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, fun r hr => ?_, e3O,
      by rw [e3N]; exact hsx, by rw [e3M]; exact hdx, ?_, ?_⟩
    · rw [k3 180 (by omega) (by omega) (by omega) (by omega)]; exact h180
    · rw [k3 182 (by omega) (by omega) (by omega) (by omega)]; exact h182
    · rw [k3 181 (by omega) (by omega) (by omega) (by omega)]; exact h181
    · rw [k3 284 (by omega) (by omega) (by omega) (by omega)]; exact h284
    · rw [k3 285 (by omega) (by omega) (by omega) (by omega)]; exact h285
    · exact k3 r (by omega) (by omega) (by omega) (by omega)
    · rw [e3R]
    · rw [e3N, e3M]
      refine hS.congr_pA (fun t k σ ht' hk' hσ => ?_) (fun y hy => Or.inr hy)
      unfold pend
      refine ⟨fun ⟨h1, h2⟩ => ⟨h1, by omega⟩, fun ⟨h1, h2⟩ => ⟨h1, ?_⟩⟩
      rcases Nat.eq_or_lt_of_le h2 with h2 | h2
      · subst h2
        have := ((src_eq_iff (lt_of_lt_of_le hσ hbNc_le)).1 h1).1
        rw [this] at hk'; exact absurd hk' hk
      · omega
    · rw [e3N]; unfold lvC; omega
/-! ### Settling a vertex -/

/-- The cost of settling `x`, besides the potential of the activations. -/
def settleCost (P : Prm) (x : ℕ) : ℕ :=
  25 * lg P.N + 13 + (if x < P.b then P.Lv * lvC P + 7 else 2) +
    (P.off (x + 1) - P.off x) * (decCost P.N + 15) + 6

/-- **Settling the vertex `x = r180` at the popped key `κ = rr180`** (its distance `dK`,
`κ = dK - p x`): the ghost run is extended by `x`, and the state of the run is restored. -/
theorem settle_exec (hL : Lay P) (hDc : Crossing P.b P.D) (hF : Feas P) {K : ℕ}
    {v : ℕ → ℕ} {d : ℕ → ℤ} {κ : ℝ} {xe : ℕ → Prop} {X : ℕ → ℕ → ℕ → Prop} {dK : ℤ}
    (c : Config) (hc : WordsBounded P.W c) (hG : Glob P c) (hX : GX P c) (hDa : Data P c)
    (hS : MSt P K v d κ F2 xe F2 X c.nmem c.rmem) (hx : c.nreg 180 < P.N)
    (hsx : sfV P c.nmem (c.nreg 180) = 0) (hxe : ∀ y, xe y → y = c.nreg 180)
    (hκ : c.rreg 180 = κ) (hdK : κ = ((dK - P.p (c.nreg 180) : ℤ) : ℝ)) :
    ∃ c' k', Exec I P.W settle c c' k' ∧
      k' + potN P c'.nmem ≤ settleCost P (c.nreg 180) + potN P c.nmem ∧
      MSt P (K + 1) (Function.update v K (c.nreg 180)) (Function.update d K dK) κ F2 F1 F2 X
        c'.nmem c'.rmem ∧
      Glob P c' ∧ GX P c' ∧ Data P c' ∧ (∀ r < 100, c'.nreg r = c.nreg r) ∧
      (∀ r < 100, c'.rreg r = c.rreg r) ∧ c'.output = c.output := by
  have hw := lay_w hL
  have := hL.m1; have := hL.m2; have := hL.m3; have := hL.m4; have := hL.m5; have := hL.m6
  have htb := tb_ge P
  generalize hx' : c.nreg 180 = x at hx hsx hxe hdK ⊢
  unfold settle
  refine spec_seq ?_
  exec_block
  · rw [hG.r109, hx']; omega
  · config_simp; rw [hG.r103, hx']; omega
  · config_simp; rw [hG.r108, hx']; omega
  · config_simp; rw [hG.r107, hx']; omega
  · config_simp; rw [hG.r100, hx']; omega
  generalize hc₁ : (Config.mk _ _ _ _ _ _ : Config) = c₁
  have hw₁ : WordsBounded P.W c₁ := hc₁ ▸ ‹_›
  have f170 : c₁.nreg 170 = (P.N + x) / 2 := by
    rw [← hc₁]; config_simp; rw [hG.r100, hx', hG.r111]
  have fK : ∀ r, r ≠ 170 → r ≠ 187 → c₁.nreg r = c.nreg r := fun r h1 h2 => by
    rw [← hc₁]; config_simp; upd_tac
  have fR : ∀ r, r ≠ 181 → c₁.rreg r = c.rreg r := fun r h1 => by
    rw [← hc₁]; config_simp; upd_tac
  have fN : ∀ a, c₁.nmem a =
      if a = P.sb + x then 1 else if a = P.wb + x then 0 else c.nmem a := fun a => by
    rw [← hc₁]; config_simp; rw [hG.r109, hx', hG.r107, hG.r117, hG.r110]
    simp only [upd_apply]
  have fM : ∀ a, c₁.rmem a = if a = P.db + x then κ + P.p x else c.rmem a := fun a => by
    rw [← hc₁]; config_simp; rw [hG.r103, hx', hG.r108, hDa.pmem x hx, hκ]
    simp only [upd_apply]
  have fO : c₁.output = c.output := by rw [← hc₁]
  have hG₁ : Glob P c₁ := hG.of fun r h1 h2 => fK r (by omega) (by omega)
  have epr : ∀ y, y ≠ x → prV P c₁.nmem y = prV P c.nmem y := fun y hy => by
    unfold prV; rw [fN]; split_ifs <;> first | rfl | omega
  have ekey : ∀ y, y ≠ x → keyV P c₁.rmem y = keyV P c.rmem y := fun y hy => by
    unfold keyV; rw [fM]; split_ifs <;> first | rfl | omega
  have hW₁ : WinOK P.N (prV P c₁.nmem) (keyV P c₁.rmem) (wnV P c₁.nmem) ((P.N + x) / 2) :=
    (hS.hp.win.set epr ekey).congr_wn fun i h1 h2 => by
      unfold wnV; rw [fN]; split_ifs <;> first | rfl | omega
  have hpr₁ : ∀ y < P.N, prV P c₁.nmem y ≤ 1 := fun y hy => by
    by_cases hyx : y = x
    · subst hyx; unfold prV; rw [fN]; split_ifs <;> omega
    · rw [epr y hyx]; exact hS.hp.pr_le y hy
  refine spec_seq ?_
  refine spec_use (hpUp_exec (I := I) hL c₁ hw₁ hG₁ (by rw [f170]; omega) hpr₁
    (by rw [f170]; exact hW₁)) ?_
  intro c₂ k₂ hk₂ hw₂ ⟨hW₂, hK₂, hR₂, hO₂, hN₂, hM₂⟩
  rw [f170] at hk₂
  have hlg : lg ((P.N + x) / 2) ≤ lg P.N := lg_mono (by omega)
  have hW₂' : WinOK P.N (prV P c₂.nmem) (keyV P c₂.rmem) (wnV P c₂.nmem) 0 :=
    hW₂.congr (fun y hy => by unfold prV; rw [hN₂ _ (Or.inl (by omega))])
      (fun y hy => by unfold keyV; rw [hM₂])
  have hS₂ := hS.header hL (dK := dK) (nm₂ := c₂.nmem) (rm₂ := c₂.rmem) hx hsx hxe
    (by rw [hN₂ _ (Or.inl (by omega)), fN]; simp only [↓reduceIte])
    (by rw [hN₂ _ (Or.inl (by omega)), fN]; split_ifs <;> first | rfl | omega)
    (by rw [hM₂, fM]; simp only [↓reduceIte]; rw [hdK]; push_cast; ring)
    (fun a h1 h2 h3 => by rw [hN₂ a h3, fN]; split_ifs <;> first | rfl | omega)
    (fun a h1 => by rw [hM₂, fM]; split_ifs <;> first | rfl | omega) hW₂'
  have g180 : c₂.nreg 180 = x := by rw [hK₂ 180 (by omega), fK 180 (by omega) (by omega), hx']
  have hG₂ : Glob P c₂ := hG₁.of fun r h1 h2 => hK₂ r (by omega)
  have hX₂ : GX P c₂ := hX.of fun r h1 h2 => by
    rw [hK₂ r (by omega)]; exact fK r (by omega) (by omega)
  have hDa₂ : Data P c₂ := hDa.of hL
    (fun a ha => by rw [hN₂ a (Or.inl (by omega)), fN]; split_ifs <;> first | rfl | omega)
    (fun a ha => by rw [hM₂, fM]; split_ifs <;> first | rfl | omega)
  have hxs₂ : sfV P c₂.nmem x = 1 := by
    unfold sfV; rw [hN₂ _ (Or.inl (by omega)), fN]; simp only [↓reduceIte]
  have hdx₂ : dV P c₂.rmem x = κ + P.p x := by
    unfold dV; rw [hM₂, fM]; simp only [↓reduceIte]
  have hhi₂ : ∀ a, P.tb ≤ a → c₂.nmem a = c.nmem a := fun a ha => by
    rw [hN₂ a (Or.inr (by omega)), fN]; split_ifs <;> first | rfl | omega
  have hpot₂ : potN P c₂.nmem = potN P c.nmem := potN_congr fun t k ht hk y hy => by
    have := tb_le_tbQ (P := P) (t := t) (k := k); unfold tPr; exact hhi₂ _ (by omega)
  -- the levels
  refine spec_seq ?_
  obtain ⟨c₃, k₃, e₃, hk₃, hG₃, hDa₃, h180₃, hK₃, hR₃, hO₃, hX₃, hdx₃, hS₃⟩ : ∃ c₃ k₃,
      Exec I P.W (.ifLtN 180 101 lvls .skip) c₂ c₃ k₃ ∧
      k₃ + potN P c₃.nmem ≤ (if x < P.b then P.Lv * lvC P + 7 else 2) + potN P c₂.nmem ∧
      Glob P c₃ ∧ Data P c₃ ∧ c₃.nreg 180 = x ∧ (∀ r < 100, c₃.nreg r = c₂.nreg r) ∧
      (∀ r < 100, c₃.rreg r = c₂.rreg r) ∧ c₃.output = c₂.output ∧ GX P c₃ ∧
      dV P c₃.rmem x = κ + P.p x ∧
      MSt P (K + 1) (Function.update v K x) (Function.update d K dK) κ F2 F1
        (arcEx x (P.off x)) X c₃.nmem c₃.rmem := by
    by_cases hxb : x < P.b
    · refine spec_ifLtN_true (by rw [g180, hG₂.r101]; exact hxb) ?_
      unfold lvls
      refine spec_seq ?_
      exec_block
      · exact Nat.zero_le _
      generalize hc₄ : (Config.mk _ _ _ _ _ _ : Config) = c₄
      have hw₄ : WordsBounded P.W c₄ := hc₄ ▸ ‹_›
      have fK4 : ∀ r, r ≠ 181 → r ≠ 182 → r ≠ 284 → r ≠ 285 → c₄.nreg r = c₂.nreg r :=
        fun r h1 h2 h3 h4 => by rw [← hc₄]; config_simp; upd_tac
      have hI₄ : LI P (K + 1) (Function.update v K x) (Function.update d K dK) κ X x c₂ 0 c₄ :=
        ⟨hw₄, hG₂.of fun r h1 h2 => fK4 r (by omega) (by omega) (by omega) (by omega),
          hX₂.of fun r h1 h2 => fK4 r (by omega) (by omega) (by omega) (by omega),
          hDa₂.of hL (fun a _ => by rw [← hc₄]) (fun a _ => by rw [← hc₄]),
          by rw [fK4 180 (by omega) (by omega) (by omega) (by omega)]; exact g180,
          by rw [← hc₄]; config_simp; rw [hG₂.r110]; rfl,
          by rw [← hc₄]; config_simp; rw [hX₂.r246]; ring,
          by rw [← hc₄]; config_simp; rw [hX₂.r240]; ring,
          by rw [← hc₄]; config_simp; ring, Nat.zero_le _,
          fun r hr => fK4 r (by omega) (by omega) (by omega) (by omega),
          fun r _ => by rw [← hc₄], by rw [← hc₄], by rw [← hc₄]; exact hxs₂,
          by rw [← hc₄]; exact hdx₂, by rw [← hc₄]; exact hS₂⟩
      obtain ⟨t₁, c₅, k₅, e₅, hI₅, hn₅, hk₅⟩ := whileLtN_ghost_pot (P' := I) (W := P.W)
        (a := 182) (b := 101) (body := lvl)
        (LI P (K + 1) (Function.update v K x) (Function.update d K dK) κ X x c₂)
        (fun t c => potN P c.nmem + (P.Lv - t) * lvC P) (fun _ _ h => h.wb)
        (fun t c hI hlt => by
          obtain ⟨c', k', e, h1, h2⟩ := lvl_exec hL hDc hF hxb c hI hlt
          exact ⟨t + 1, c', k', e, h1, h2⟩) hI₄
      refine ⟨c₅, k₅, e₅, ?_⟩
      rw [hI₅.r182, hI₅.glob.r101] at hn₅
      have hS₅ := hI₅.si.pend_end (Or.inl hn₅)
      have e4N : c₄.nmem = c₂.nmem := by rw [← hc₄]
      refine ⟨?_, hI₅.glob, hI₅.data, hI₅.r180, hI₅.keepN, hI₅.keepR, hI₅.out, hI₅.gx, hI₅.dx,
        hS₅⟩
      rw [iteT hxb, ← e4N]
      have : (P.Lv - 0) * lvC P = P.Lv * lvC P := by rw [Nat.sub_zero]
      rw [this] at hk₅
      omega
    · refine spec_ifLtN_false (by rw [g180, hG₂.r101]; exact hxb) ?_
      refine spec_skip hw₂ ⟨?_, hG₂, hDa₂, g180, fun _ _ => rfl, fun _ _ => rfl, rfl, hX₂,
        hdx₂, hS₂.pend_end (Or.inr hxb)⟩
      rw [iteF hxb]
  refine ⟨c₃, k₃, e₃, ?_⟩
  have hw₃ := e₃.wb_right
  refine spec_use (arcs_exec (I := I) hL hF hx (i := K) (by omega) (Function.update_self ..)
    c₃ hw₃ hG₃ hDa₃ h180₃ hdx₃ hS₃) ?_
  intro c₄ k₄ hk₄ hw₄ ⟨hG₄, hDa₄, hK₄, hR₄, hO₄, hhi₄, hS₄⟩
  have hpot₄ : potN P c₄.nmem = potN P c₃.nmem := potN_congr fun t k ht hk y hy => by
    have := tb_le_tbQ (P := P) (t := t) (k := k); unfold tPr; exact hhi₄ _ (by omega)
  refine ⟨?_, hS₄, hG₄, hX₃.of fun r h1 h2 => hK₄ r (by omega), hDa₄, fun r hr => ?_,
    fun r hr => ?_, ?_⟩
  · rw [hpot₄, ← hpot₂]
    unfold settleCost
    split_ifs at hk₃ ⊢ <;> omega
  · rw [hK₄ r (by omega), hK₃ r hr, hK₂ r (by omega), fK r (by omega) (by omega)]
  · rw [hR₄ r hr, hR₃ r hr, hR₂ r (by omega), fR r (by omega)]
  · rw [hO₄, hO₃, hO₂, fO]

end FR

end Monge

end PlanarFlow
