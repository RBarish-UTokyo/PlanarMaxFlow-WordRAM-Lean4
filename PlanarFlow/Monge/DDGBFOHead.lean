module

public import PlanarFlow.Monge.DDGBF2Round
public import PlanarFlow.Monge.ExtMonge

/-!
# A round over a dense distance graph with missing arcs: the invariant, the tables, a half block

The one-matrix level loop of `PlanarFlow/Monge/DDGBF.lean` relaxes the arcs of a *complete*
dense distance graph block by block, with SMAWK on Monge half blocks. Here the dense distance
graph may miss arcs: the arc `i → j` exists when `X i j`, with the length `D i j`, and the lengths
satisfy the crossing inequality in the extended sense (`CrossingX`, the form
`PlanarFlow.Monge.CrossingO` takes with `X = isSome`, `D = getD 0`). A half block is then Monge
only in the extended sense, and SMAWK is run on the totally monotone copied matrix of
`PlanarFlow/Monge/ExtMonge.lean` (`extA`), whose entries `subMul · e + subVal` do not depend on
the values `e`: the program reads them from two static tables.

* `RoundGX b X D Q lo hi C E₀ E flag`: `PlanarFlow.Monge.RoundG` with only the arcs `X`
  (and the start values `E₀ ≤ 0`, which bound the finite entries below the replacements).
* `hbOf b s t`: the half block (`r0, nr, c1, nc`) of the level loop holding the pair `(s, t)`
  (`hbOf_first`, `hbOf_second`: it is the half block in which the level loop meets the pair).
* `tVal`, `tMul`, `finB`: the tables, at `Vb + 2 (s b + t)` (real: `tVal`; natural: `finB`, the
  arc flag) and `Vb + 2 (s b + t) + 1` (real: `tMul`) (`EnvO`, layout `LayO`).
* `entO`: the entry oracle `tMul · e s + tVal`; `updBodyO`: the update of a target, only when the
  minimum found is an arc into it (`finB = 1`); `halfO`: a half block. `halfO_exec`: a half block
  relaxes all the arcs from its sources to its targets.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace Monge

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

/-! ### The crossing inequality with missing arcs -/

/-- **The crossing inequality with missing arcs** (the arc `i → j` exists when `X i j`): for
interleaved ends, if the arcs `i → j` and `i' → j'` exist, so do `i → j'` and `i' → j`, and
`D i j' + D i' j ≤ D i j + D i' j'`. -/
def CrossingX (b : ℕ) (X : ℕ → ℕ → Prop) (D : ℕ → ℕ → ℤ) : Prop :=
  ∀ i i' j j', i < i' → j < j' → i' < b → j' < b → (i' < j ∨ j' < i) → X i j → X i' j' →
    X i j' ∧ X i' j ∧ D i j' + D i' j ≤ D i j + D i' j'

/-! ### The invariant of a round, with missing arcs -/

/-- `RoundG` restricted to the arcs `X`, with nonpositive start values. -/
structure RoundGX (b : ℕ) (X : ℕ → ℕ → Prop) (D : ℕ → ℕ → ℤ) (Q : Prop) (lo hi : ℕ → ℤ)
    (C : ℕ → ℕ → Prop) (E₀ E : ℕ → ℤ) (flag : ℕ) : Prop where
  top : ∀ v < b, E₀ v ≤ 0
  pot : Q → ∀ i j, i < b → j < b → i ≠ j → X i j → lo j ≤ lo i + D i j
  le : ∀ v < b, E v ≤ E₀ v
  chg : (flag = 0 ∧ ∀ v < b, E v = E₀ v) ∨ (flag = 1 ∧ ∃ v < b, E v < E₀ v)
  feas : flag = 0 → ∀ i j, i < b → j < b → i ≠ j → X i j → C i j → E j ≤ E i + D i j
  bf : Q → (∀ v < b, lo v ≤ E v ∧ E₀ v ≤ hi v) ∧
    ∀ i j, i < b → j < b → i ≠ j → X i j → C i j → E j ≤ hi i + D i j

variable {b : ℕ} {X : ℕ → ℕ → Prop} {D : ℕ → ℕ → ℤ} {Q : Prop} {lo hi : ℕ → ℤ}

/-- The start of a round. -/
theorem RoundGX.start {E : ℕ → ℤ} (htop : ∀ v < b, E v ≤ 0)
    (hpot : Q → ∀ i j, i < b → j < b → i ≠ j → X i j → lo j ≤ lo i + D i j)
    (h : Q → ∀ v < b, lo v ≤ E v ∧ E v ≤ hi v) :
    RoundGX b X D Q lo hi (fun _ _ => False) E E 0 :=
  ⟨htop, hpot, fun _ _ => le_rfl, Or.inl ⟨rfl, fun _ _ => rfl⟩, fun _ _ _ _ _ _ _ h => h.elim,
    fun hQ => ⟨h hQ, fun _ _ _ _ _ _ h => h.elim⟩⟩

/-- Fewer processed arcs. -/
theorem RoundGX.mono {C C' : ℕ → ℕ → Prop} {E₀ E : ℕ → ℤ} {flag : ℕ}
    (h : RoundGX b X D Q lo hi C E₀ E flag)
    (hC : ∀ i j, i < b → j < b → i ≠ j → X i j → C' i j → C i j) :
    RoundGX b X D Q lo hi C' E₀ E flag :=
  ⟨h.top, h.pot, h.le, h.chg,
    fun hf i j hi hj hij hx hc => h.feas hf i j hi hj hij hx (hC i j hi hj hij hx hc),
    fun hP => ⟨(h.bf hP).1, fun i j hi hj hij hx hc =>
      (h.bf hP).2 i j hi hj hij hx (hC i j hi hj hij hx hc)⟩⟩

/-- **One target lowered to the minimum over a set of sources with an arc into it.** -/
theorem RoundGX.update {C : ℕ → ℕ → Prop} {E₀ E : ℕ → ℤ} {flag : ℕ}
    (h : RoundGX b X D Q lo hi C E₀ E flag)
    {S : ℕ → Prop} {t : ℕ} (ht : t < b) (hS : ∀ i, S i → i < b ∧ i ≠ t ∧ X i t) {V : ℤ}
    (hV1 : ∀ i, S i → V ≤ E i + D i t) (hV2 : ∃ i, S i ∧ V = E i + D i t) :
    RoundGX b X D Q lo hi (fun i j => C i j ∨ (S i ∧ j = t)) E₀
      (fun v => if v = t ∧ V < E t then V else E v) (if V < E t then 1 else flag) := by
  obtain ⟨htop, hpot, hle, hfl, hfe, hbf⟩ := h
  by_cases hV : V < E t
  · simp only [hV, and_true, ite_true]
    refine ⟨htop, hpot, fun v hv => ?_, Or.inr ⟨rfl, t, ht, ?_⟩, fun h => absurd h one_ne_zero,
      fun hP => ?_⟩
    · split_ifs with e
      · subst e; exact hV.le.trans (hle v hv)
      · exact hle v hv
    · simp only [ite_true]; exact lt_of_lt_of_le hV (hle t ht)
    · obtain ⟨h1, h2⟩ := hbf hP
      obtain ⟨i₀, hi₀, hVi₀⟩ := hV2
      refine ⟨fun v hv => ⟨?_, (h1 v hv).2⟩, fun i j hi hj hij hx hc => ?_⟩
      · split_ifs with e
        · subst e
          have := hpot hP i₀ v (hS i₀ hi₀).1 hv (hS i₀ hi₀).2.1 (hS i₀ hi₀).2.2
          have := (h1 i₀ (hS i₀ hi₀).1).1
          omega
        · exact (h1 v hv).1
      · split_ifs with e
        · subst e
          rcases hc with hc | ⟨hc, -⟩
          · have := h2 i j hi hj hij hx hc; omega
          · have := hV1 i hc
            have := hle i hi
            have := (h1 i hi).2
            omega
        · rcases hc with hc | ⟨-, hc⟩
          · exact h2 i j hi hj hij hx hc
          · exact absurd hc e
  · simp only [hV, and_false, ite_false]
    refine ⟨htop, hpot, hle, hfl, fun hf i j hi hj hij hx hc => ?_,
      fun hP => ⟨(hbf hP).1, fun i j hi hj hij hx hc => ?_⟩⟩
    · rcases hc with hc | ⟨hc, rfl⟩
      · exact hfe hf i j hi hj hij hx hc
      · have := hV1 i hc; omega
    · rcases hc with hc | ⟨hc, rfl⟩
      · exact (hbf hP).2 i j hi hj hij hx hc
      · have := hV1 i hc
        have := hle i hi
        have := ((hbf hP).1 i hi).2
        omega

/-- The flag of a round is `0` or `1`. -/
theorem RoundGX.flag_le {C : ℕ → ℕ → Prop} {E₀ E : ℕ → ℤ} {flag : ℕ}
    (h : RoundGX b X D Q lo hi C E₀ E flag) : flag ≤ 1 := by
  rcases h.chg with ⟨h, -⟩ | ⟨h, -⟩ <;> omega

/-- The values of a round are nonpositive. -/
theorem RoundGX.nonpos {C : ℕ → ℕ → Prop} {E₀ E : ℕ → ℤ} {flag : ℕ}
    (h : RoundGX b X D Q lo hi C E₀ E flag) : ∀ v < b, E v ≤ 0 :=
  fun v hv => (h.le v hv).trans (h.top v hv)

/-! ### The half block of a pair -/

/-- Equal quotients by `2 ^ a` stay equal by larger powers. -/
lemma div_pow_eq_of_le {s t a c : ℕ} (h : s / 2 ^ a = t / 2 ^ a) (hac : a ≤ c) :
    s / 2 ^ c = t / 2 ^ c := by
  induction c, hac using Nat.le_induction with
  | base => exact h
  | succ c _ ih => exact div_pow_succ_eq ih

/-- The level of the pair `(s, t)`: the least `T` with `s` and `t` in one block of size
`2 ^ (T + 1)`. -/
noncomputable def levOf (s t : ℕ) : ℕ := by
  classical exact if h : ∃ T, s / 2 ^ (T + 1) = t / 2 ^ (T + 1) then Nat.find h else 0

/-- The level of a pair split at `T`. -/
lemma levOf_eq {s t T : ℕ} (h1 : s / 2 ^ (T + 1) = t / 2 ^ (T + 1))
    (h2 : s / 2 ^ T ≠ t / 2 ^ T) : levOf s t = T := by
  classical
  have hex : ∃ T, s / 2 ^ (T + 1) = t / 2 ^ (T + 1) := ⟨T, h1⟩
  unfold levOf
  rw [dite_eq_left_of_eq_true (eq_true hex), Nat.find_eq_iff]
  exact ⟨h1, fun n hn hp => h2 (div_pow_eq_of_le hp (by omega))⟩

/-- **The half block of the level loop holding the pair `(s, t)`**: `(r0, nr, c1, nc)`, the
targets `r0 … r0 + nr - 1` and the sources `c1 - nc … c1 - 1`. -/
noncomputable def hbOf (b s t : ℕ) : ℕ × ℕ × ℕ × ℕ :=
  if s < t then
    (2 * 2 ^ levOf s t * (s / (2 * 2 ^ levOf s t)) + 2 ^ levOf s t,
      min (2 * 2 ^ levOf s t * (s / (2 * 2 ^ levOf s t)) + 2 ^ levOf s t + 2 ^ levOf s t) b -
        (2 * 2 ^ levOf s t * (s / (2 * 2 ^ levOf s t)) + 2 ^ levOf s t),
      2 * 2 ^ levOf s t * (s / (2 * 2 ^ levOf s t)) + 2 ^ levOf s t, 2 ^ levOf s t)
  else
    (2 * 2 ^ levOf s t * (s / (2 * 2 ^ levOf s t)), 2 ^ levOf s t,
      min (2 * 2 ^ levOf s t * (s / (2 * 2 ^ levOf s t)) + 2 ^ levOf s t + 2 ^ levOf s t) b,
      min (2 * 2 ^ levOf s t * (s / (2 * 2 ^ levOf s t)) + 2 ^ levOf s t + 2 ^ levOf s t) b -
        (2 * 2 ^ levOf s t * (s / (2 * 2 ^ levOf s t)) + 2 ^ levOf s t))

/-- The quotient of a number in `[sz q, sz q + sz)`. -/
lemma div_of_mem {x sz q : ℕ} (_hsz : 0 < sz) (h1 : sz * q ≤ x) (h2 : x < sz * q + sz) :
    x / sz = q :=
  Nat.div_eq_of_lt_le (by rw [Nat.mul_comm]; exact h1) (by rw [Nat.succ_mul, Nat.mul_comm]; omega)

/-- The level of a pair in the two halves of the block `[2 sz q, 2 sz q + 2 sz)`. -/
lemma levOf_block {sz T q s t : ℕ} (hsz : sz = 2 ^ T) (hs1 : 2 * sz * q ≤ s)
    (hs2 : s < 2 * sz * q + 2 * sz) (ht1 : 2 * sz * q ≤ t) (ht2 : t < 2 * sz * q + 2 * sz)
    (hne : s / sz ≠ t / sz) : levOf s t = T ∧ s / (2 * sz) = q := by
  have hpos : 0 < sz := by rw [hsz]; exact Nat.two_pow_pos T
  have e2 : 2 ^ (T + 1) = 2 * sz := by rw [pow_succ, hsz]; ring
  have hsq : s / (2 * sz) = q := div_of_mem (by omega) hs1 hs2
  have htq : t / (2 * sz) = q := div_of_mem (by omega) ht1 ht2
  refine ⟨levOf_eq (by rw [e2, hsq, htq]) (by rw [← hsz]; exact hne), hsq⟩

/-- **The first half of a block**: sources `[base, base + sz)`, targets `[base + sz, rend)`. -/
theorem hbOf_first {b sz T q base s t : ℕ} (hsz : sz = 2 ^ T) (hb : base = 2 * sz * q)
    (hs1 : base ≤ s) (hs2 : s < base + sz) (ht1 : base + sz ≤ t)
    (ht2 : t < min (base + sz + sz) b) :
    hbOf b s t = (base + sz, min (base + sz + sz) b - (base + sz), base + sz, sz) := by
  have hpos : 0 < sz := by rw [hsz]; exact Nat.two_pow_pos T
  have hs : s / sz = 2 * q := div_of_mem hpos (by rw [hb] at hs1; linarith)
    (by rw [hb] at hs2; linarith)
  have ht : t / sz = 2 * q + 1 := div_of_mem hpos (by rw [hb] at ht1; linarith)
    (by have := min_le_left (base + sz + sz) b; rw [hb] at ht2 this; nlinarith)
  obtain ⟨hl, hq⟩ := levOf_block (q := q) (s := s) (t := t) hsz (by omega) (by omega) (by omega)
    (by have := min_le_left (base + sz + sz) b; omega) (by omega)
  unfold hbOf
  rw [ite_eq_left_of_eq_true _ _ (eq_true (show s < t by omega)), hl, ← hsz, hq, ← hb]

/-- **The second half of a block**: sources `[base + sz, rend)`, targets `[base, base + sz)`. -/
theorem hbOf_second {b sz T q base s t : ℕ} (hsz : sz = 2 ^ T) (hb : base = 2 * sz * q)
    (ht1 : base ≤ t) (ht2 : t < base + sz) (hs1 : base + sz ≤ s)
    (hs2 : s < min (base + sz + sz) b) :
    hbOf b s t = (base, sz, min (base + sz + sz) b, min (base + sz + sz) b - (base + sz)) := by
  have hpos : 0 < sz := by rw [hsz]; exact Nat.two_pow_pos T
  have ht : t / sz = 2 * q := div_of_mem hpos (by rw [hb] at ht1; linarith)
    (by rw [hb] at ht2; linarith)
  have hs : s / sz = 2 * q + 1 := div_of_mem hpos (by rw [hb] at hs1; linarith)
    (by have := min_le_left (base + sz + sz) b; rw [hb] at hs2 this; nlinarith)
  obtain ⟨hl, hq⟩ := levOf_block (q := q) (s := s) (t := t) hsz (by omega)
    (by have := min_le_left (base + sz + sz) b; omega) (by omega) (by omega) (by omega)
  unfold hbOf
  rw [ite_eq_right_of_eq_false _ _ (eq_false (show ¬ s < t by omega)), hl, ← hsz, hq, ← hb]

/-! ### The tables -/

/-- The arc pattern of the half block `(r0, c1)`: row `ρ` is the target `r0 + ρ`, column `κ` the
source `c1 - 1 - κ`. -/
def Fb (X : ℕ → ℕ → Prop) (r0 c1 : ℕ) (ρ κ : ℕ) : Prop := X (c1 - 1 - κ) (r0 + ρ)

/-- The lengths of the half block `(r0, c1)`. -/
def Drb (D : ℕ → ℕ → ℤ) (r0 c1 : ℕ) (ρ κ : ℕ) : ℝ := (D (c1 - 1 - κ) (r0 + ρ) : ℝ)

/-- The matrix of a half block given to SMAWK, for the values `E`. -/
noncomputable def blkO (X : ℕ → ℕ → Prop) (D : ℕ → ℕ → ℤ) (H : ℝ) (E : ℕ → ℤ)
    (r0 nr c1 nc : ℕ) : ℕ → ℕ → ℝ :=
  extA nr nc (Fb X r0 c1) (Drb D r0 c1) H (fun κ => (E (c1 - 1 - κ) : ℝ))

/-- The constant part of the entry of the pair `(s, t)`, in its half block. -/
noncomputable def tVal (b : ℕ) (X : ℕ → ℕ → Prop) (D : ℕ → ℕ → ℤ) (H : ℝ) (s t : ℕ) : ℝ :=
  subVal (hbOf b s t).2.1 (hbOf b s t).2.2.2 (Fb X (hbOf b s t).1 (hbOf b s t).2.2.1)
    (Drb D (hbOf b s t).1 (hbOf b s t).2.2.1) H (t - (hbOf b s t).1) ((hbOf b s t).2.2.1 - 1 - s)

/-- The multiplier of the value of the source of the entry of the pair `(s, t)`. -/
noncomputable def tMul (b : ℕ) (X : ℕ → ℕ → Prop) (s t : ℕ) : ℝ :=
  subMul (hbOf b s t).2.1 (hbOf b s t).2.2.2 (Fb X (hbOf b s t).1 (hbOf b s t).2.2.1)
    (t - (hbOf b s t).1) ((hbOf b s t).2.2.1 - 1 - s)

/-- The arc flag. -/
noncomputable def finB (X : ℕ → ℕ → Prop) (s t : ℕ) : ℕ := by
  classical exact if X s t then 1 else 0

/-- The arc flag is `0` or `1`. -/
lemma finB_le (s t : ℕ) : finB X s t ≤ 1 := by
  classical unfold finB; split_ifs <;> omega

/-- The table of constants on a half block of the level loop. -/
lemma tVal_blk {r0 nr c1 nc ρ κ : ℕ} (hhb : hbOf b (c1 - 1 - κ) (r0 + ρ) = (r0, nr, c1, nc))
    (hκ : κ < c1) (H : ℝ) :
    tVal b X D H (c1 - 1 - κ) (r0 + ρ) = subVal nr nc (Fb X r0 c1) (Drb D r0 c1) H ρ κ := by
  unfold tVal; rw [hhb]
  simp only
  rw [show r0 + ρ - r0 = ρ by omega, show c1 - 1 - (c1 - 1 - κ) = κ by omega]

/-- The table of multipliers on a half block of the level loop. -/
lemma tMul_blk {r0 nr c1 nc ρ κ : ℕ} (hhb : hbOf b (c1 - 1 - κ) (r0 + ρ) = (r0, nr, c1, nc))
    (hκ : κ < c1) :
    tMul b X (c1 - 1 - κ) (r0 + ρ) = subMul nr nc (Fb X r0 c1) ρ κ := by
  unfold tMul; rw [hhb]
  simp only
  rw [show r0 + ρ - r0 = ρ by omega, show c1 - 1 - (c1 - 1 - κ) = κ by omega]

/-- **A half block of the level loop is totally monotone after the replacement.** -/
theorem blkO_totMono (hD : CrossingX b X D) {H : ℝ}
    (hH : ∀ s t, s < b → t < b → X s t → (D s t : ℝ) + b < H) {E : ℕ → ℤ}
    (htop : ∀ v < b, E v ≤ 0) {r0 nr c1 nc : ℕ} (hnc : nc ≤ c1) (hc1 : c1 ≤ b)
    (hr : r0 + nr ≤ b) (hsep : r0 + nr ≤ c1 - nc ∨ c1 ≤ r0) :
    IsTotMono nr nc (blkO X D H E r0 nr c1 nc) := by
  refine extA_totMono ?_ ?_
  · intro ρ ρ' κ κ' h1 h2 h3 h4 hb' hc'
    have key := hD (c1 - 1 - κ') (c1 - 1 - κ) (r0 + ρ) (r0 + ρ') (by omega) (by omega) (by omega)
      (by omega) (by omega) hb' hc'
    refine ⟨key.2.1, key.1, ?_⟩
    simp only [Drb]
    have k2 : ((D (c1 - 1 - κ') (r0 + ρ') + D (c1 - 1 - κ) (r0 + ρ) : ℤ) : ℝ) ≤
        ((D (c1 - 1 - κ') (r0 + ρ) + D (c1 - 1 - κ) (r0 + ρ') : ℤ) : ℝ) :=
      Int.cast_le.2 key.2.2
    push_cast at k2
    linarith
  · intro ρ hρ κ hκ hF
    have h1 := hH (c1 - 1 - κ) (r0 + ρ) (by omega) (by omega) hF
    have h2 : ((E (c1 - 1 - κ) : ℤ) : ℝ) ≤ 0 := by exact_mod_cast htop _ (by omega)
    have h3 : (nc : ℝ) ≤ b := by exact_mod_cast (show nc ≤ b by omega)
    simp only [Drb]
    linarith

/-! ### The data in memory -/

/-- The fixed registers and the tables. -/
structure EnvO (b Vb eb pb : ℕ) (X : ℕ → ℕ → Prop) (D : ℕ → ℕ → ℤ) (H : ℝ) (c : Config) :
    Prop where
  r1 : c.nreg 1 = b
  r2 : c.nreg 2 = Vb
  r3 : c.nreg 3 = eb
  r4 : c.nreg 4 = pb
  r10 : c.nreg 10 = 1
  z10 : c.rreg 10 = 0
  val : ∀ s t, s < b → t < b → s ≠ t → c.rmem (Vb + 2 * (s * b + t)) = tVal b X D H s t
  mul : ∀ s t, s < b → t < b → s ≠ t → c.rmem (Vb + 2 * (s * b + t) + 1) = tMul b X s t
  fin : ∀ s t, s < b → t < b → s ≠ t → c.nmem (Vb + 2 * (s * b + t)) = finB X s t

/-- The layout of the memory and the word bound. -/
structure LayO (b Vb eb pb W : ℕ) : Prop where
  pe : pb + 5 * b + 1 < eb
  ed : eb + b ≤ Vb
  w : Vb + 2 * (b * b) + 4 * b + 10 ≤ W

variable {Vb eb pb : ℕ} {H : ℝ}

/-- The tables survive a step with the given frame. -/
theorem EnvO.of {c c' : Config} (h : EnvO b Vb eb pb X D H c)
    (hn : ∀ r, r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 10 → c'.nreg r = c.nreg r)
    (hr : c'.rreg 10 = c.rreg 10) (hm : ∀ a, Vb ≤ a → c'.rmem a = c.rmem a)
    (hnm : ∀ a, Vb ≤ a → c'.nmem a = c.nmem a) : EnvO b Vb eb pb X D H c' :=
  ⟨(hn 1 (by omega)).trans h.r1, (hn 2 (by omega)).trans h.r2, (hn 3 (by omega)).trans h.r3,
    (hn 4 (by omega)).trans h.r4, (hn 10 (by omega)).trans h.r10, hr.trans h.z10,
    fun s t hs ht hst => (hm _ (by omega)).trans (h.val s t hs ht hst),
    fun s t hs ht hst => (hm _ (by omega)).trans (h.mul s t hs ht hst),
    fun s t hs ht hst => (hnm _ (by omega)).trans (h.fin s t hs ht hst)⟩

/-! ### The program -/

/-- The entry oracle of a half block: `tMul · e s + tVal` for the source `s = r25 - 1 - r71` and
the target `t = r24 + r70`. -/
def entO : Stmt := block [.subN 80 25 10, .subN 80 80 71, .addN 81 24 70, .addN 82 3 80,
  .loadR 80 82, .mulN 83 80 1, .addN 83 83 81, .addN 83 83 83, .addN 83 83 2, .loadR 81 83,
  .addN 84 83 10, .loadR 82 84, .mulR 82 82 80, .addR 70 82 81]

/-- One step of the update of a half block: lower the target `r24 + r26` to the minimum of the
row `r26`, when the column of that minimum is an arc into the target. -/
def updBodyO : Stmt :=
  .seq (block [.addN 27 24 26, .addN 28 3 27, .addN 29 4 26, .addN 29 29 10, .loadR 20 29,
      .loadR 21 28, .loadN 29 29, .subN 29 25 29, .subN 29 29 10, .mulN 29 29 1, .addN 29 29 27,
      .addN 29 29 29, .addN 29 29 2, .loadN 29 29])
    (.seq (.ifLtN 29 10 .skip (.ifLtR 20 21 (block [.storeR 28 20, .constN 30 1]) .skip))
      (.instr (.addN 26 26 10)))

/-- A half block. -/
def halfO : Stmt :=
  .seq (.instr (.copyN 62 4)) <| .seq (smawk entO) <| .seq (.instr (.constN 26 0))
    (.whileLtN 26 60 updBodyO)

/-- A block `[r21, r21 + 2s)`: both halves. -/
def blockBodyO : Stmt :=
  .seq (.instr (.addN 23 22 20)) <| .seq (.ifLtN 1 23 (.instr (.copyN 23 1)) .skip) <|
  .seq (block [.copyN 24 22, .copyN 25 22, .subN 60 23 22, .copyN 61 20]) <| .seq halfO <|
  .seq (block [.copyN 24 21, .copyN 25 23, .copyN 60 20, .subN 61 23 22]) <| .seq halfO <|
  block [.addN 21 21 20, .addN 21 21 20, .addN 22 21 20]

/-- A level `s = r20`: all its blocks, then `s := 2s`. -/
def levelBFO : Stmt :=
  .seq (block [.constN 21 0, .copyN 22 20]) (.seq (.whileLtN 22 1 blockBodyO)
    (.instr (.addN 20 20 20)))

variable {P : Input} {W : ℕ}

/-- **The entry oracle.** -/
theorem entO_exec (hL : LayO b Vb eb pb W) {E : ℕ → ℤ} {r0 nr c1 nc : ℕ} {c₀ : Config}
    (hE : EnvO b Vb eb pb X D H c₀) (hV : Vals b eb E c₀) (h24 : c₀.nreg 24 = r0)
    (h25 : c₀.nreg 25 = c1) (hnc : nc ≤ c1) (hc1 : c1 ≤ b) (hr : r0 + nr ≤ b)
    (hsep : r0 + nr ≤ c1 - nc ∨ c1 ≤ r0)
    (hhb : ∀ ρ < nr, ∀ κ < nc, hbOf b (c1 - 1 - κ) (r0 + ρ) = (r0, nr, c1, nc)) :
    EntSpecK P W entO (blkO X D H E r0 nr c1 nc) 14 nr nc pb (4 * nr + nc + 1) c₀ := by
  intro c hc hA h70 h71
  obtain ⟨a1, a2, a3, a4, a5⟩ := hA
  have g1 : c.nreg 1 = b := (a1 1 (by omega)).trans hE.r1
  have g2 : c.nreg 2 = Vb := (a1 2 (by omega)).trans hE.r2
  have g3 : c.nreg 3 = eb := (a1 3 (by omega)).trans hE.r3
  have g10 : c.nreg 10 = 1 := (a1 10 (by omega)).trans hE.r10
  have g24 : c.nreg 24 = r0 := (a1 24 (by omega)).trans h24
  have g25 : c.nreg 25 = c1 := (a1 25 (by omega)).trans h25
  have hLw := hL.w
  have hLe := hL.ed
  have hpe := hL.pe
  generalize hρ : c.nreg 70 = ρ at h70
  generalize hκ : c.nreg 71 = κ at h71
  have hsrc : c1 - 1 - κ < b := by omega
  have hsb : (c1 - 1 - κ) * b + b ≤ b * b := by
    have := Nat.mul_le_mul_right b (show c1 - 1 - κ + 1 ≤ b by omega)
    rw [Nat.add_mul, Nat.one_mul] at this; exact this
  have hs1 : c1 - 1 = c1 - 1 - κ + κ := by omega
  unfold entO
  exec_block
  · config_simp; rw [g24, hρ]; omega
  · config_simp; rw [g3, g25, g10, hκ]; omega
  · config_simp; rw [g25, g10, hκ, g1]; omega
  · config_simp; rw [g25, g10, hκ, g1, g24, hρ]; omega
  · config_simp; rw [g25, g10, hκ, g1, g24, hρ]; omega
  · config_simp; rw [g25, g10, hκ, g1, g24, hρ, g2]; omega
  · config_simp; rw [g25, g10, hκ, g1, g24, hρ, g2]; omega
  refine ⟨le_refl _, ?_, fun r hr => ?_, fun r hr h => ?_, rfl, rfl, rfl⟩
  · config_simp
    rw [g25, g10, hκ, g1, g24, hρ, g2, g3]
    have hs : c1 - 1 - κ = c1 - 1 - κ := rfl
    have e1 : c.rmem (eb + (c1 - 1 - κ)) = E (c1 - 1 - κ) := by
      rw [a4 _ (Or.inr (by omega))]; exact hV _ hsrc
    have e2 : c.rmem ((c1 - 1 - κ) * b + (r0 + ρ) + ((c1 - 1 - κ) * b + (r0 + ρ)) + Vb) =
        subVal nr nc (Fb X r0 c1) (Drb D r0 c1) H ρ κ := by
      rw [a4 _ (Or.inr (by omega)),
        show (c1 - 1 - κ) * b + (r0 + ρ) + ((c1 - 1 - κ) * b + (r0 + ρ)) + Vb =
          Vb + 2 * ((c1 - 1 - κ) * b + (r0 + ρ)) by ring,
        hE.val _ _ hsrc (by omega) (by omega), tVal_blk (hhb ρ h70 κ h71) (by omega)]
    have e3 : c.rmem ((c1 - 1 - κ) * b + (r0 + ρ) + ((c1 - 1 - κ) * b + (r0 + ρ)) + Vb + 1) =
        subMul nr nc (Fb X r0 c1) ρ κ := by
      rw [a4 _ (Or.inr (by omega)),
        show (c1 - 1 - κ) * b + (r0 + ρ) + ((c1 - 1 - κ) * b + (r0 + ρ)) + Vb + 1 =
          Vb + 2 * ((c1 - 1 - κ) * b + (r0 + ρ)) + 1 by ring,
        hE.mul _ _ hsrc (by omega) (by omega), tMul_blk (hhb ρ h70 κ h71) (by omega)]
    rw [e1, e2, e3]
    rfl
  · config_simp; upd_tac
  · config_simp; upd_tac

/-! ### The update of a half block -/

/-- The arcs of a half block processed so far (as in `HalfArcs`). -/
structure IUpO (b Vb eb : ℕ) (X : ℕ → ℕ → Prop) (D : ℕ → ℕ → ℤ) (W : ℕ) (Q : Prop)
    (lo hi : ℕ → ℤ) (C : ℕ → ℕ → Prop) (E₀ E₁ : ℕ → ℤ) (r0 nr c1 nc : ℕ) (c₁ c : Config) :
    Prop where
  wb : WordsBounded W c
  nreg : ∀ r, r ≠ 26 → r ≠ 27 → r ≠ 28 → r ≠ 29 → r ≠ 30 → c.nreg r = c₁.nreg r
  rreg : ∀ r, r ≠ 20 → r ≠ 21 → c.rreg r = c₁.rreg r
  nmem : c.nmem = c₁.nmem
  rmem : ∀ a, (a < eb + r0 ∨ eb + r0 + nr ≤ a) → c.rmem a = c₁.rmem a
  out : c.output = c₁.output
  ρ : c.nreg 26 ≤ nr
  vals : ∃ E, Vals b eb E c ∧
    RoundGX b X D Q lo hi (fun i j => C i j ∨ HalfArcs r0 c1 nc (c.nreg 26) i j) E₀ E
      (c.nreg 30) ∧
    ∀ v < b, (v < r0 ∨ r0 + c.nreg 26 ≤ v) → E v = E₁ v

/-- One step of the update of a half block. -/
theorem updBodyO_exec (hH : ∀ s t, s < b → t < b → X s t → (D s t : ℝ) + b < H)
    (hL : LayO b Vb eb pb W) {C : ℕ → ℕ → Prop} {E₀ E₁ : ℕ → ℤ}
    {r0 nr c1 nc : ℕ} {c₁ : Config} (hE₁ : EnvO b Vb eb pb X D H c₁) (h24 : c₁.nreg 24 = r0)
    (h25 : c₁.nreg 25 = c1) (h60 : c₁.nreg 60 = nr) (hnc : 1 ≤ nc) (hnc' : nc ≤ c1)
    (hc1 : c1 ≤ b) (hr : r0 + nr ≤ b) (hsep : r0 + nr ≤ c1 - nc ∨ c1 ≤ r0)
    (htop : ∀ v < b, E₁ v ≤ 0)
    (hrow : ∀ ρ < nr, c₁.nmem (pb + ρ + 1) = lmin nc (blkO X D H E₁ r0 nr c1 nc) ρ ∧
      c₁.rmem (pb + ρ + 1) = blkO X D H E₁ r0 nr c1 nc ρ (lmin nc (blkO X D H E₁ r0 nr c1 nc) ρ))
    (c : Config) (hI : IUpO b Vb eb X D W Q lo hi C E₀ E₁ r0 nr c1 nc c₁ c)
    (hlt : c.nreg 26 < c.nreg 60) :
    ∃ c' k', Exec P W updBodyO c c' k' ∧ IUpO b Vb eb X D W Q lo hi C E₀ E₁ r0 nr c1 nc c₁ c' ∧
      22 * (nr - c'.nreg 26) + k' + 2 ≤ 22 * (nr - c.nreg 26) := by
  have hc := hI.wb
  have hLw := hL.w
  have hpe := hL.pe
  have hed := hL.ed
  have g : ∀ r, r ≠ 26 → r ≠ 27 → r ≠ 28 → r ≠ 29 → r ≠ 30 → c.nreg r = c₁.nreg r := hI.nreg
  have g1 : c.nreg 1 = b :=
    (g 1 (by omega) (by omega) (by omega) (by omega) (by omega)).trans hE₁.r1
  have g2 : c.nreg 2 = Vb :=
    (g 2 (by omega) (by omega) (by omega) (by omega) (by omega)).trans hE₁.r2
  have g3 : c.nreg 3 = eb :=
    (g 3 (by omega) (by omega) (by omega) (by omega) (by omega)).trans hE₁.r3
  have g4 : c.nreg 4 = pb :=
    (g 4 (by omega) (by omega) (by omega) (by omega) (by omega)).trans hE₁.r4
  have g10 : c.nreg 10 = 1 :=
    (g 10 (by omega) (by omega) (by omega) (by omega) (by omega)).trans hE₁.r10
  have g24 : c.nreg 24 = r0 :=
    (g 24 (by omega) (by omega) (by omega) (by omega) (by omega)).trans h24
  have g25 : c.nreg 25 = c1 :=
    (g 25 (by omega) (by omega) (by omega) (by omega) (by omega)).trans h25
  rw [g 60 (by omega) (by omega) (by omega) (by omega) (by omega), h60] at hlt
  generalize hρ : c.nreg 26 = ρ at hlt
  have hρI := hI.ρ
  rw [hρ] at hρI
  obtain ⟨E, hV, hR, hE⟩ := hI.vals
  rw [hρ] at hR hE
  -- the minimum found by SMAWK
  set A := blkO X D H E₁ r0 nr c1 nc with hA
  have hn0 : 0 < nc := hnc
  have hκs : lmin nc A ρ < nc := lmin_lt A ρ hn0
  generalize hκd : lmin nc A ρ = κs at hκs
  have hrow' := hrow ρ hlt
  rw [hκd] at hrow'
  have hnmρ : c.nmem (pb + ρ + 1) = κs := by rw [hI.nmem]; exact hrow'.1
  have hrowc : c.rmem (pb + ρ + 1) = A ρ κs := by
    rw [hI.rmem _ (Or.inl (by omega))]; exact hrow'.2
  have htc : c.rmem (eb + (r0 + ρ)) = E (r0 + ρ) := hV _ (by omega)
  generalize hsd : c1 - 1 - κs = sd
  have hsdb : sd < b := by omega
  have hsb : sd * b + b ≤ b * b := by
    have := Nat.mul_le_mul_right b (show sd + 1 ≤ b by omega)
    rw [Nat.add_mul, Nat.one_mul] at this; exact this
  have hfin : c.nmem (Vb + 2 * (sd * b + (r0 + ρ))) = finB X sd (r0 + ρ) := by
    rw [hI.nmem]; exact hE₁.fin _ _ hsdb (by omega) (by omega)
  have hsrc : ∀ i, c1 - nc ≤ i → i < c1 → E i = E₁ i := fun i h1 h2 => hE i (by omega) (by omega)
  unfold updBodyO
  refine spec_seq ?_
  exec_block
  · rw [g24, hρ]; omega
  · config_simp; rw [g3, g24, hρ]; omega
  · config_simp; rw [g4, hρ]; omega
  · config_simp; rw [g4, hρ, g10]; omega
  · config_simp; rw [g25, g4, hρ, g10, hnmρ, g1, show c1 - κs - 1 = sd by omega]; omega
  · config_simp; rw [g25, g4, hρ, g10, hnmρ, g1, g24, show c1 - κs - 1 = sd by omega]; omega
  · config_simp; rw [g25, g4, hρ, g10, hnmρ, g1, g24, show c1 - κs - 1 = sd by omega]; omega
  · config_simp; rw [g25, g4, hρ, g10, hnmρ, g1, g24, g2, show c1 - κs - 1 = sd by omega]
    omega
  have hcfg : c.nmem (sd * b + (r0 + ρ) + (sd * b + (r0 + ρ)) + Vb) = finB X sd (r0 + ρ) := by
    rw [show sd * b + (r0 + ρ) + (sd * b + (r0 + ρ)) + Vb = Vb + 2 * (sd * b + (r0 + ρ)) by
      ring]; exact hfin
  have hreg : ∀ x : ℕ, (c.nreg 25 - c.nmem (c.nreg 4 + c.nreg 26 + c.nreg 10) - c.nreg 10) *
      c.nreg 1 + (c.nreg 24 + c.nreg 26) + ((c.nreg 25 - c.nmem (c.nreg 4 + c.nreg 26 +
      c.nreg 10) - c.nreg 10) * c.nreg 1 + (c.nreg 24 + c.nreg 26)) + c.nreg 2 = x →
      x = sd * b + (r0 + ρ) + (sd * b + (r0 + ρ)) + Vb := by
    intro x hx
    rw [← hx, g25, g4, hρ, g10, hnmρ, g1, g24, g2, show c1 - κs - 1 = sd by omega]
  refine spec_seq ?_
  by_cases hX : X sd (r0 + ρ)
  · -- an arc: the row is genuine and the minimum is an arc into the target
    have hf1 : finB X sd (r0 + ρ) = 1 := by
      classical unfold finB; rw [ite_eq_left_of_eq_true _ _ (eq_true hX)]
    have hg : GRow nr nc (Fb X r0 c1) ρ := ⟨hlt, κs, hκs, by
      show X (c1 - 1 - κs) (r0 + ρ); rw [hsd]; exact hX⟩
    have hbnd : ∀ ρ' < nr, ∀ κ < nc, Fb X r0 c1 ρ' κ →
        (E₁ (c1 - 1 - κ) : ℝ) + Drb D r0 c1 ρ' κ + nc < H := fun ρ' hρ' κ hκ hF => by
      have h1 := hH (c1 - 1 - κ) (r0 + ρ') (by omega) (by omega) hF
      have h2 : ((E₁ (c1 - 1 - κ) : ℤ) : ℝ) ≤ 0 := by exact_mod_cast htop _ (by omega)
      have h3 : (nc : ℝ) ≤ b := by exact_mod_cast (show nc ≤ b by omega)
      simp only [Drb]; linarith
    obtain ⟨-, hval, hmin⟩ := extA_lmin (Hs := H) (Dr := Drb D r0 c1)
      (e := fun κ => (E₁ (c1 - 1 - κ) : ℝ)) hbnd hg
    rw [show lmin nc (extA nr nc (Fb X r0 c1) (Drb D r0 c1) H fun κ => (E₁ (c1 - 1 - κ) : ℝ)) ρ
      = κs from hκd] at hval hmin
    set V : ℤ := E₁ sd + D sd (r0 + ρ) with hVd
    have hAV : A ρ κs = (V : ℝ) := by
      rw [hA]; unfold blkO; rw [hval]; simp only [Drb, hsd, hVd]; push_cast; ring
    have hS : ∀ i, (c1 - nc ≤ i ∧ i < c1 ∧ X i (r0 + ρ)) → i < b ∧ i ≠ r0 + ρ ∧ X i (r0 + ρ) :=
      fun i hi => ⟨by omega, by omega, hi.2.2⟩
    have hV1 : ∀ i, (c1 - nc ≤ i ∧ i < c1 ∧ X i (r0 + ρ)) → V ≤ E i + D i (r0 + ρ) := by
      intro i hi
      have := hmin (c1 - 1 - i) (by omega) (by
        show X (c1 - 1 - (c1 - 1 - i)) (r0 + ρ); rw [show c1 - 1 - (c1 - 1 - i) = i by omega]
        exact hi.2.2)
      simp only [Drb] at this
      rw [show c1 - 1 - (c1 - 1 - i) = i by omega] at this
      rw [hsrc i hi.1 hi.2.1]
      have h' : (V : ℝ) ≤ ((E₁ i + D i (r0 + ρ) : ℤ) : ℝ) := by
        rw [← hAV, hA]; unfold blkO; push_cast; exact this
      exact_mod_cast h'
    have hV2 : ∃ i, (c1 - nc ≤ i ∧ i < c1 ∧ X i (r0 + ρ)) ∧ V = E i + D i (r0 + ρ) :=
      ⟨sd, ⟨by omega, by omega, hX⟩, by rw [hsrc sd (by omega) (by omega)]⟩
    have hU := hR.update (S := fun i => c1 - nc ≤ i ∧ i < c1 ∧ X i (r0 + ρ)) (t := r0 + ρ)
      (by omega) hS hV1 hV2
    have hfin' : ∀ c' : Config, WordsBounded W c' →
        (∀ r, r ≠ 26 → r ≠ 27 → r ≠ 28 → r ≠ 29 → r ≠ 30 → c'.nreg r = c.nreg r) →
        (∀ r, r ≠ 20 → r ≠ 21 → c'.rreg r = c.rreg r) → c'.nmem = c.nmem →
        c'.output = c.output → c'.nreg 26 = ρ + 1 →
        c'.nreg 30 = (if V < E (r0 + ρ) then 1 else c.nreg 30) →
        (∀ a, c'.rmem a = if a = eb + (r0 + ρ) ∧ V < E (r0 + ρ) then ((V : ℤ) : ℝ)
          else c.rmem a) →
        IUpO b Vb eb X D W Q lo hi C E₀ E₁ r0 nr c1 nc c₁ c' := by
      intro c' hw hn' hr' hnm ho h26 h30 hrm
      refine ⟨hw, fun r a1 a2 a3 a4 a5 => (hn' r a1 a2 a3 a4 a5).trans (g r a1 a2 a3 a4 a5),
        fun r a1 a2 => (hr' r a1 a2).trans (hI.rreg r a1 a2), hnm.trans hI.nmem, fun a ha => ?_,
        ho.trans hI.out, by omega, ?_⟩
      · rw [hrm a]; split_ifs with h
        · omega
        · exact hI.rmem a ha
      · refine ⟨fun v => if v = r0 + ρ ∧ V < E (r0 + ρ) then V else E v, fun v hv => ?_, ?_,
          fun v hv hv' => ?_⟩
        · rw [hrm]
          by_cases h : v = r0 + ρ ∧ V < E (r0 + ρ)
          · have h' : eb + v = eb + (r0 + ρ) ∧ V < E (r0 + ρ) := ⟨by rw [h.1], h.2⟩
            rw [ite_eq_left_of_eq_true _ _ (eq_true h')]; beta_reduce
            rw [ite_eq_left_of_eq_true _ _ (eq_true h)]
          · have h' : ¬ (eb + v = eb + (r0 + ρ) ∧ V < E (r0 + ρ)) :=
              fun h'' => h ⟨by omega, h''.2⟩
            rw [ite_eq_right_of_eq_false _ _ (eq_false h')]; beta_reduce
            rw [ite_eq_right_of_eq_false _ _ (eq_false h)]; exact hV v hv
        · rw [h30, h26]
          refine hU.mono fun i j hi hj hij hx hc => ?_
          rcases hc with hc | ⟨h1, h2, h3, h4⟩
          · exact Or.inl (Or.inl hc)
          · by_cases hj' : j = r0 + ρ
            · subst hj'; exact Or.inr ⟨⟨h1, h2, hx⟩, rfl⟩
            · exact Or.inl (Or.inr ⟨h1, h2, h3, by omega⟩)
        · rw [h26] at hv'
          simp only
          split_ifs with h
          · omega
          · exact hE v hv (by omega)
    refine spec_ifLtN_false (by
      config_simp; rw [hreg _ rfl, hcfg, hf1, g10]; omega) ?_
    have hcmpR : ∀ x : ℝ, (x < c.rmem (c.nreg 3 + (c.nreg 24 + c.nreg 26)) ↔
        x < (E (r0 + ρ) : ℝ)) ∧ c.rmem (c.nreg 4 + c.nreg 26 + c.nreg 10) = (V : ℝ) := fun x => by
      rw [g4, hρ, g10, g3, g24, hrowc, htc, hAV]; exact ⟨Iff.rfl, rfl⟩
    by_cases hcmp : V < E (r0 + ρ)
    · refine spec_ifLtR_true (by
        config_simp; rw [(hcmpR 0).2, (hcmpR _).1]; exact_mod_cast hcmp) ?_
      exec_block
      · omega
      refine spec_instr (Exec.addN ‹_› _ _ _ ?_) fun hw => ?_
      · config_simp; rw [hρ, g10]; omega
      refine ⟨hfin' _ hw (fun r a1 a2 a3 a4 a5 => ?_) (fun r a1 a2 => ?_) rfl rfl ?_ ?_ ?_, ?_⟩
      · config_simp; upd_tac
      · config_simp; upd_tac
      · config_simp; rw [hρ, g10]
      · config_simp; simp only [hcmp, ite_true]
      · intro a; config_simp; rw [upd_apply, (hcmpR 0).2, g3, g24, hρ]
        split_ifs with h1 h2 h2
        · rfl
        · exact absurd ⟨h1, hcmp⟩ h2
        · exact absurd h2.1 h1
        · rfl
      · config_simp; rw [hρ, g10]; omega
    · refine spec_ifLtR_false (by
        config_simp; rw [(hcmpR 0).2, (hcmpR _).1]; exact_mod_cast hcmp) ?_
      refine spec_skip ‹_› ?_
      refine spec_instr (Exec.addN ‹_› _ _ _ ?_) fun hw => ?_
      · config_simp; rw [hρ, g10]; omega
      refine ⟨hfin' _ hw (fun r a1 a2 a3 a4 a5 => ?_) (fun r a1 a2 => ?_) rfl rfl ?_ ?_ ?_, ?_⟩
      · config_simp; upd_tac
      · config_simp; upd_tac
      · config_simp; rw [hρ, g10]
      · config_simp; simp only [hcmp, ite_false]
      · intro a; config_simp
        split_ifs with h1
        · exact absurd h1.2 hcmp
        · rfl
      · config_simp; rw [hρ, g10]; omega
  · -- no arc at the minimum: the row has no arc at all, nothing to relax
    have hf0 : finB X sd (r0 + ρ) = 0 := by
      classical unfold finB; rw [ite_eq_right_of_eq_false _ _ (eq_false hX)]
    have hnone : ∀ i, c1 - nc ≤ i → i < c1 → ¬ X i (r0 + ρ) := by
      intro i h1 h2 hXi
      have hg : GRow nr nc (Fb X r0 c1) ρ := ⟨hlt, c1 - 1 - i, by omega, by
        show X (c1 - 1 - (c1 - 1 - i)) (r0 + ρ); rw [show c1 - 1 - (c1 - 1 - i) = i by omega]
        exact hXi⟩
      have hbnd : ∀ ρ' < nr, ∀ κ < nc, Fb X r0 c1 ρ' κ →
          (E₁ (c1 - 1 - κ) : ℝ) + Drb D r0 c1 ρ' κ + nc < H := fun ρ' hρ' κ hκ hF => by
        have h1 := hH (c1 - 1 - κ) (r0 + ρ') (by omega) (by omega) hF
        have h2 : ((E₁ (c1 - 1 - κ) : ℤ) : ℝ) ≤ 0 := by exact_mod_cast htop _ (by omega)
        have h3 : (nc : ℝ) ≤ b := by exact_mod_cast (show nc ≤ b by omega)
        simp only [Drb]; linarith
      have := (extA_lmin (Hs := H) (Dr := Drb D r0 c1)
        (e := fun κ => (E₁ (c1 - 1 - κ) : ℝ)) hbnd hg).1
      rw [show lmin nc (extA nr nc (Fb X r0 c1) (Drb D r0 c1) H fun κ => (E₁ (c1 - 1 - κ) : ℝ))
        ρ = κs from hκd] at this
      exact hX (by rw [← hsd]; exact this)
    refine spec_ifLtN_true (by config_simp; rw [hreg _ rfl, hcfg, hf0, g10]; omega) ?_
    refine spec_skip ‹_› ?_
    refine spec_instr (Exec.addN ‹_› _ _ _ ?_) fun hw => ?_
    · config_simp; rw [hρ, g10]; omega
    refine ⟨⟨hw, fun r a1 a2 a3 a4 a5 => ?_, fun r a1 a2 => ?_, rfl.trans hI.nmem,
      fun a ha => ?_, hI.out, ?_, E, fun v hv => ?_, ?_, fun v hv hv' => ?_⟩, ?_⟩
    · config_simp; rw [← g r a1 a2 a3 a4 a5]; upd_tac
    · config_simp; rw [← hI.rreg r a1 a2]; upd_tac
    · config_simp; exact hI.rmem a ha
    · config_simp; rw [hρ, g10]; omega
    · config_simp; exact hV v hv
    · config_simp; rw [hρ, g10]
      refine hR.mono fun i j hi hj hij hx hc => ?_
      rcases hc with hc | ⟨h1, h2, h3, h4⟩
      · exact Or.inl hc
      · by_cases hj' : j = r0 + ρ
        · subst hj'; exact absurd hx (hnone i h1 h2)
        · exact Or.inr ⟨h1, h2, h3, by omega⟩
    · config_simp at hv'; rw [hρ, g10] at hv'
      exact hE v hv (by omega)
    · config_simp; rw [hρ, g10]; omega

end Monge

end PlanarFlow
