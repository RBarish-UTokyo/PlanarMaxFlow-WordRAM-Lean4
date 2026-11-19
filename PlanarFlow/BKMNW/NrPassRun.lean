module

public import PlanarFlow.BKMNW.NrPass

/-!
# One pass of the cancellation on the machine: the run of `nrPass`

**`nrPass_exec`** (see `NrPass.lean`): within `nrPassCost m n` steps, a `DkP` whose out-lists are
the darts by key, heads `NH`, lengths `Z - G`, its distances `Dv` (`dkProg_exec`), and
`G[i] := G[i] + Dv NH[i] - Dv KY[i]`; memory changed only in the scratch and in `G`.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace PlanarFlow

namespace BKMNW

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs NegSSSP Monge.FR

variable {P : Input} {W : ℕ}

/-- Two ranges `[a, a + m)` and `[b, b + k)` are disjoint (a definition, so that `omega` does not
split it unless asked). -/
def NrSep (a m b k : ℕ) : Prop := a + m ≤ b ∨ b + k ≤ a

/-- The well-formedness of Dijkstra's parameters in `nrPass`. -/
lemma nrPass_dkG {m n NH Z S s Inf : ℕ} (mem : ℕ → ℕ) (hn : 0 < n) (hs : s < n)
    (dN : NrSep NH m S (3 * m + 8 * n + 1)) (wS : S + 3 * m + 8 * n + 1 ≤ W)
    (wN : NH + m ≤ W) (wI : 2 * Z + Inf ≤ W)
    (hob : ∀ y < n, ∃ len, mem (S + 2 * m + 3 * n + 1 + y) = mem (S + 2 * m + 2 * n + 1 + y) + len ∧
      mem (S + 2 * m + 3 * n + 1 + y) ≤ m)
    (harc : ∀ y < n, ∀ i, mem (S + 2 * m + 2 * n + 1 + y) ≤ i → i < mem (S + 2 * m + 3 * n + 1 + y) →
      mem (S + 2 * m + 4 * n + 1 + i) < m)
    (hLN : ∀ j < m, mem (S + j) ≤ Z)
    (hNH : ∀ j < m, mem (NH + j) < n) :
    DkG (dkPOf n (S + 3 * m + 4 * n + 1) (S + 3 * m + 5 * n + 1) (S + 2 * m + 2 * n + 1)
      (S + 2 * m + 3 * n + 1) (S + 2 * m + 4 * n + 1) NH S Inf s mem) W := by
  have hob' : ∀ y < n, mem (S + 2 * m + 2 * n + 1 + y) ≤ mem (S + 2 * m + 3 * n + 1 + y) ∧
      mem (S + 2 * m + 3 * n + 1 + y) ≤ m := fun y hy => by
    obtain ⟨l, h1, h2⟩ := hob y hy; omega
  set p := dkPOf n (S + 3 * m + 4 * n + 1) (S + 3 * m + 5 * n + 1) (S + 2 * m + 2 * n + 1)
    (S + 2 * m + 3 * n + 1) (S + 2 * m + 4 * n + 1) NH S Inf s mem with hp
  have hout : ∀ a, (a < S + 3 * m + 4 * n + 1 ∨ S + 3 * m + 8 * n + 1 ≤ a) → ¬ DkOut p a :=
    fun a ha => (dkPOf_out).not.2 (by omega)
  have pob : ∀ y, p.ob y = mem (S + 2 * m + 2 * n + 1 + y) := fun _ => rfl
  have poe : ∀ y, p.oe y = mem (S + 2 * m + 3 * n + 1 + y) := fun _ => rfl
  have pol : ∀ i, p.ol i = mem (S + 2 * m + 4 * n + 1 + i) := fun _ => rfl
  have pB : p.OBb = S + 2 * m + 2 * n + 1 := rfl
  have pE : p.OEb = S + 2 * m + 3 * n + 1 := rfl
  have pL : p.OLb = S + 2 * m + 4 * n + 1 := rfl
  have pH : p.NHb = NH := rfl
  have pN : p.Lb = S := rfl
  refine ⟨hn, hs, by show S + 3 * m + 4 * n + 1 + n ≤ W; omega,
    by show S + 3 * m + 5 * n + 1 + 3 * n ≤ W; omega,
    Or.inl (by show S + 3 * m + 4 * n + 1 + n ≤ S + 3 * m + 5 * n + 1; omega),
    by show Inf ≤ W; omega, fun y hy => by rw [pob, poe]; exact (hob' y hy).1,
    fun y hy => ⟨by show S + 2 * m + 2 * n + 1 + y ≤ W; have : y < n := hy; omega,
      hout _ (by have : y < n := hy; omega)⟩,
    fun y hy => ⟨by show S + 2 * m + 3 * n + 1 + y ≤ W; have : y < n := hy; omega,
      hout _ (by have : y < n := hy; omega)⟩, fun y hy i h1 h2 => ?_,
    fun y hy i h1 h2 => ?_, fun y hy i h1 h2 => ?_, fun y hy i h1 h2 => ?_,
    fun y hy i h1 h2 => ?_⟩
  all_goals
    have hy' : y < n := hy
    rw [pob] at h1
    rw [poe] at h2
    have ho := (hob' y hy').2
    have ha := harc y hy' i h1 h2
  · exact ⟨by show S + 2 * m + 4 * n + 1 + i ≤ W; omega, hout _ (by omega)⟩
  · rw [pol]
    exact ⟨by show NH + _ ≤ W; omega, hout _ (by rcases dN with h | h <;> omega)⟩
  · rw [pol]
    exact ⟨by show S + _ ≤ W; omega, hout _ (by omega)⟩
  · rw [pol]
    show mem (NH + mem (S + 2 * m + 4 * n + 1 + i)) < n
    exact hNH _ ha
  · rw [pol]
    show Inf + mem (S + mem (S + 2 * m + 4 * n + 1 + i)) ≤ W
    have := hLN _ ha; omega

set_option maxHeartbeats 4000000 in
/-- **One pass of the cancellation on the machine** (see the module docstring). -/
theorem nrPass_exec (c : Config) (hc : WordsBounded W c) {m n Gb KY NH Z S s Inf : ℕ}
    (r0 : c.nreg 9000 = m) (r1 : c.nreg 9001 = n) (r2 : c.nreg 9002 = Gb)
    (r3 : c.nreg 9003 = KY) (r4 : c.nreg 9004 = NH) (r5 : c.nreg 9005 = Z)
    (r6 : c.nreg 9006 = S) (r7 : c.nreg 9007 = s) (r8 : c.nreg 9008 = Inf)
    (hm : 0 < m) (hn : 0 < n) (hs : s < n)
    (hK : ∀ i < m, c.nmem (KY + i) < n ∧ c.nmem (NH + i) < n)
    (hG2 : ∀ i < m, c.nmem (Gb + i) ≤ 2 * Z)
    (dG : NrSep Gb m S (3 * m + 8 * n + 1)) (dK : NrSep KY m S (3 * m + 8 * n + 1))
    (dN : NrSep NH m S (3 * m + 8 * n + 1)) (d1 : NrSep Gb m KY m) (d2 : NrSep Gb m NH m)
    (wS : S + 3 * m + 8 * n + 1 ≤ W) (wG : Gb + m ≤ W) (wK : KY + m ≤ W) (wN : NH + m ≤ W)
    (wI : 2 * Z + Inf ≤ W) (wm : m + 1 ≤ W) (wn : n + 1 ≤ W) :
    ∃ c' t, Exec P W nrPass c c' t ∧ t ≤ nrPassCost m n ∧
      ∃ p : DkP, p.n = n ∧ p.s = s ∧ p.Inf = Inf ∧
        (∀ y < n, ∀ i, p.ob y ≤ i → i < p.oe y → p.ol i < m ∧ c.nmem (KY + p.ol i) = y) ∧
        (∀ j < m, ∃ i, p.ob (c.nmem (KY + j)) ≤ i ∧ i < p.oe (c.nmem (KY + j)) ∧ p.ol i = j) ∧
        (∀ j < m, p.nh j = c.nmem (NH + j)) ∧ (∀ j < m, p.ln j = Z - c.nmem (Gb + j)) ∧
        ∃ Dv : ℕ → ℕ, (∀ y < n, Dv y ≤ Inf ∧ (Dv y < Inf → DkReach p y (Dv y)) ∧
            ∀ L, DkReach p y L → Dv y ≤ L) ∧
          (∀ i < m, c'.nmem (Gb + i) =
            c.nmem (Gb + i) + Dv (c.nmem (NH + i)) - Dv (c.nmem (KY + i))) ∧
          (∀ a, (a < S ∨ S + 3 * m + 8 * n + 1 ≤ a) → (a < Gb ∨ Gb + m ≤ a) →
            c'.nmem a = c.nmem a) ∧
          (∀ x, x < 1500 ∨ (1520 < x ∧ x < 2500) ∨ (2547 < x ∧ x < 9010) ∨ 9024 < x →
            c'.nreg x = c.nreg x) ∧
          c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  -- 1. the bases
  obtain ⟨c₁, t₁, e₁, ht₁, a10, a11, a12, a13, a14, a15, a16, a17, a18, f₁, m₁, rr₁, rm₁, o₁⟩ :=
    nrPA_exec (P := P) c hc r0 r1 r6 wS
  have q₁ : ∀ x, (x < 9010 ∨ 9018 < x) → c₁.nreg x = c.nreg x := f₁
  -- 2. `i := 0`
  obtain ⟨c₂, t₂, e₂, ht₂, b19, f₂, m₂, rr₂, rm₂, o₂⟩ := nrI0_exec (P := P) c₁ e₁.wb_right
  have q₂ : ∀ x, (x < 9010 ∨ 9019 < x) → c₂.nreg x = c.nreg x := fun x hx => by
    rw [f₂ x (by omega), q₁ x (by omega)]
  have p₂ : ∀ x, 9010 ≤ x → x ≤ 9018 → c₂.nreg x = c₁.nreg x := fun x h1 h2 => f₂ x (by omega)
  -- 3. loop A
  obtain ⟨c₃, t₃, e₃, ht₃, l₃, k₃, f₃, rr₃, rm₃, o₃⟩ := nrLAL_exec (P := P) c₂ e₂.wb_right
    (G := Gb) (Z := Z) (S := S) (m := m)
    (by rw [q₂ _ (by omega), r0]) (by rw [q₂ _ (by omega), r2]) (by rw [q₂ _ (by omega), r5])
    (by rw [q₂ _ (by omega), r6]) (by rw [p₂ _ (by omega) (by omega), a10])
    (by rw [p₂ _ (by omega) (by omega), a11]) b19 (by rcases dG with h | h <;> omega) wG (by omega) wm
  have mem₃ : ∀ a, (a < S ∨ S + 2 * m ≤ a) → c₃.nmem a = c.nmem a := fun a ha => by
    rw [k₃ a ha, m₂, m₁]
  have q₃ : ∀ x, (x < 9010 ∨ 9022 < x) → c₃.nreg x = c.nreg x := fun x hx => by
    rw [f₃ x (by omega), q₂ x (by omega)]
  have p₃ : ∀ x, 9010 ≤ x → x ≤ 9018 → c₃.nreg x = c₁.nreg x := fun x h1 h2 => by
    rw [f₃ x (by omega), p₂ x h1 h2]
  -- 4. the registers of `osProg`
  obtain ⟨c₄, t₄, e₄, ht₄, u0, u1, u2, u4, u5, u6, u7, u8, u9, f₄, m₄, rr₄, rm₄, o₄⟩ :=
    nrPB_exec (P := P) c₃ e₃.wb_right
  -- 5. the counting sort
  have hLay : OsLay m n KY (S + m) (S + 2 * m) (S + 2 * m + n + 1) (S + 2 * m + 2 * n + 1)
      (S + 2 * m + 3 * n + 1) (S + 2 * m + 4 * n + 1) W (fun i => c.nmem (KY + i))
      (fun _ => 1) :=
    ⟨fun i hi _ => (hK i hi).1, by omega, by rcases dK with h | h <;> omega, by omega, by omega,
      by omega, by omega, by rcases dK with h | h <;> omega, by omega, wK, by omega, by omega,
      by omega, wm, wn⟩
  have hIn : OsIn m n KY (S + m) (S + 2 * m) (S + 2 * m + n + 1) (S + 2 * m + 2 * n + 1)
      (S + 2 * m + 3 * n + 1) (S + 2 * m + 4 * n + 1) (fun i => c.nmem (KY + i))
      (fun _ => 1) c₄ :=
    ⟨by rw [u0, q₃ _ (by omega), r0], by rw [u1, q₃ _ (by omega), r1],
      by rw [u2, q₃ _ (by omega), r3], by rw [u4, p₃ _ (by omega) (by omega), a11],
      by rw [u5, p₃ _ (by omega) (by omega), a12], by rw [u6, p₃ _ (by omega) (by omega), a13],
      by rw [u7, p₃ _ (by omega) (by omega), a14], by rw [u8, p₃ _ (by omega) (by omega), a15],
      by rw [u9, p₃ _ (by omega) (by omega), a16],
      fun i hi => by rw [m₄, mem₃ _ (by rcases dK with h | h <;> omega)],
      fun i hi => by rw [m₄]; exact (l₃ i hi).2⟩
  obtain ⟨c₅, t₅, e₅, ht₅, hord, hsum, k₅, f₅, rr₅, rm₅, o₅⟩ :=
    nrOs_exec (P := P) hLay c₄ e₄.wb_right hIn
  have q₅ : ∀ x, (x < 1500 ∨ 1520 < x) → (x < 9010 ∨ 9022 < x) → c₅.nreg x = c.nreg x :=
    fun x h1 h2 => by rw [f₅ x (by omega), f₄ x (by omega), q₃ x h2]
  have p₅ : ∀ x, 9010 ≤ x → x ≤ 9018 → c₅.nreg x = c₁.nreg x := fun x h1 h2 => by
    rw [f₅ x (by omega), f₄ x (by omega), p₃ x h1 h2]
  have mem₅ : ∀ a, (a < S + 2 * m ∨ S + 2 * m + 2 * n + 1 ≤ a) →
      (a < S + 2 * m + 2 * n + 1 ∨ S + 2 * m + 4 * n + 1 + m ≤ a) → c₅.nmem a = c₄.nmem a :=
    fun a h1 h2 => k₅ a h1 h2
  -- 6. the registers of `dkProg`
  obtain ⟨c₆, t₆, e₆, ht₆, v0, v1, v2, v4, v5, v6, v7, v8, v9, v10, f₆, m₆, rr₆, rm₆, o₆⟩ :=
    nrPC_exec (P := P) c₅ e₅.wb_right
  -- the arcs
  set p := dkPOf n (S + 3 * m + 4 * n + 1) (S + 3 * m + 5 * n + 1) (S + 2 * m + 2 * n + 1)
    (S + 2 * m + 3 * n + 1) (S + 2 * m + 4 * n + 1) NH S Inf s c₆.nmem with hp
  have hob : ∀ y < n, p.oe y = p.ob y + (nrF (fun i => c.nmem (KY + i)) (fun _ => 1) m y).length ∧
      p.oe y ≤ m ∧ ∀ t (ht : t < (nrF (fun i => c.nmem (KY + i)) (fun _ => 1) m y).length),
        p.ol (p.ob y + t) = (nrF (fun i => c.nmem (KY + i)) (fun _ => 1) m y)[t] := by
    intro y hy
    obtain ⟨o1, o2, o3⟩ := hord y hy
    simp only [hp, dkPOf, m₆]
    exact ⟨o1, o2, o3⟩
  have harc : ∀ y < n, ∀ i, p.ob y ≤ i → i < p.oe y → p.ol i < m ∧ c.nmem (KY + p.ol i) = y :=
    fun y hy i h1 h2 => by
      obtain ⟨x1, -, x3⟩ := nr_ord_arc ⟨(hob y hy).1, (hob y hy).2.2⟩ h1 h2
      exact ⟨x1, x3⟩
  have hall : ∀ j < m, ∃ i, p.ob (c.nmem (KY + j)) ≤ i ∧ i < p.oe (c.nmem (KY + j)) ∧
      p.ol i = j := fun j hj => nr_ord_all (T := fun i => c.nmem (KY + i)) hj one_ne_zero
    ⟨(hob _ (hK j hj).1).1, (hob _ (hK j hj).1).2.2⟩
  -- the memory before Dijkstra
  have mem₆ : ∀ a, (a < S ∨ S + 3 * m + 8 * n + 1 ≤ a) → c₆.nmem a = c.nmem a := fun a ha => by
    rw [m₆, mem₅ a (by omega) (by omega), m₄, mem₃ a (by omega)]
  have hNH : ∀ j < m, p.nh j = c.nmem (NH + j) := fun j hj => by
    show c₆.nmem (NH + j) = _; exact mem₆ _ (by rcases dN with h | h <;> omega)
  have hLN : ∀ j < m, p.ln j = Z - c.nmem (Gb + j) := fun j hj => by
    show c₆.nmem (S + j) = _
    rw [m₆, mem₅ _ (by omega) (by omega), m₄, (l₃ j hj).1, m₂, m₁]
  have hdeg : ∑ y ∈ range p.n, (p.oe y - p.ob y) ≤ m := by
    simp only [hp, dkPOf, m₆]; exact hsum
  have hG : DkG p W := nrPass_dkG c₆.nmem hn hs dN wS wN wI
    (fun y hy => ⟨_, (hob y hy).1, (hob y hy).2.1⟩) (fun y hy i h1 h2 => (harc y hy i h1 h2).1)
    (fun j hj => by
      have := hLN j hj; change c₆.nmem (S + j) = _ at this; omega)
    (fun j hj => by
      have := hNH j hj; change c₆.nmem (NH + j) = _ at this; rw [this]; exact (hK j hj).2)
  have hDM : DkMem p c₆.nmem := ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ _ _ _ => rfl,
    fun _ _ _ _ _ => rfl, fun _ _ _ _ _ => rfl⟩
  have q₆ : ∀ x, (x < 1500 ∨ 1520 < x) → (x < 2500 ∨ 2510 < x) → (x < 9010 ∨ 9022 < x) →
      c₆.nreg x = c.nreg x := fun x h1 h2 h3 => by rw [f₆ x h2, q₅ x h1 h3]
  have p₆ : ∀ x, 9010 ≤ x → x ≤ 9018 → c₆.nreg x = c₁.nreg x := fun x h1 h2 => by
    rw [f₆ x (by omega), p₅ x h1 h2]
  -- 7. Dijkstra
  obtain ⟨c₇, t₇, e₇, ht₇, hD, k₇, f₇, rr₇, rm₇, o₇⟩ := dkProg_exec (P := P) hG c₆
    e₆.wb_right hDM (by rw [v0, q₅ _ (by omega) (by omega), r1]; rfl)
    (by rw [v1, p₅ _ (by omega) (by omega), a17]; rfl) (by rw [v2, p₅ _ (by omega) (by omega), a18]; rfl)
    (by rw [v4, p₅ _ (by omega) (by omega), a14]; rfl) (by rw [v5, p₅ _ (by omega) (by omega), a15]; rfl)
    (by rw [v6, p₅ _ (by omega) (by omega), a16]; rfl)
    (by rw [v7, q₅ _ (by omega) (by omega), r4]; rfl) (by rw [v8, q₅ _ (by omega) (by omega), r6]; rfl)
    (by rw [v9, q₅ _ (by omega) (by omega), r8]; rfl) (by rw [v10, q₅ _ (by omega) (by omega), r7]; rfl)
    hdeg
  have q₇ : ∀ x, (x < 1500 ∨ 1520 < x) → (x < 2500 ∨ 2547 < x) → (x < 9010 ∨ 9022 < x) →
      c₇.nreg x = c.nreg x := fun x h1 h2 h3 => by
    rw [f₇ x (by omega), q₆ x h1 (by omega) h3]
  have p₇ : ∀ x, 9010 ≤ x → x ≤ 9018 → c₇.nreg x = c₁.nreg x := fun x h1 h2 => by
    rw [f₇ x (by omega), p₆ x h1 h2]
  have mem₇ : ∀ a, (a < S ∨ S + 3 * m + 8 * n + 1 ≤ a) → c₇.nmem a = c.nmem a := fun a ha => by
    rw [k₇ a ((dkPOf_out).not.2 (by omega)), mem₆ a ha]
  -- 8. `i := 0`, 9. loop D
  obtain ⟨c₈, t₈, e₈, ht₈, b19', f₈, m₈, rr₈, rm₈, o₈⟩ := nrI0_exec (P := P) c₇ e₇.wb_right
  obtain ⟨c₉, t₉, e₉, ht₉, l₉, k₉, f₉, rr₉, rm₉, o₉⟩ := nrLDL_exec (P := P) c₈ e₈.wb_right
    (G := Gb) (KY := KY) (NH := NH) (Db := S + 3 * m + 4 * n + 1) (m := m)
    (by rw [f₈ _ (by omega), q₇ _ (by omega) (by omega) (by omega), r0])
    (by rw [f₈ _ (by omega), q₇ _ (by omega) (by omega) (by omega), r2])
    (by rw [f₈ _ (by omega), q₇ _ (by omega) (by omega) (by omega), r3])
    (by rw [f₈ _ (by omega), q₇ _ (by omega) (by omega) (by omega), r4])
    (by rw [f₈ _ (by omega), p₇ _ (by omega) (by omega), a10])
    (by rw [f₈ _ (by omega), p₇ _ (by omega) (by omega), a17]) b19' n
    (fun i hi => by
      rw [m₈, mem₇ _ (by rcases dK with h | h <;> omega), mem₇ _ (by rcases dN with h | h <;> omega)]
      exact hK i hi)
    d1 d2 (by rcases dG with h | h <;> omega) wG wK wN (by omega)
    (fun i hi => by
      rw [m₈, mem₇ _ (by rcases dG with h | h <;> omega), mem₇ (NH + i) (by rcases dN with h | h <;> omega)]
      have h1 : c₇.nmem (S + 3 * m + 4 * n + 1 + c.nmem (NH + i)) ≤ Inf := (hD _ ((hK i hi).2)).1
      have := hG2 i hi
      show _ + c₇.nmem (S + 3 * m + 4 * n + 1 + _) ≤ W
      omega) wm
  rw [show p.n = n from rfl] at ht₇
  refine ⟨c₉, t₁ + (t₂ + (t₃ + (t₄ + (t₅ + (t₆ + (t₇ + (t₈ + t₉))))))),
    .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ (.seq e₅ (.seq e₆ (.seq e₇ (.seq e₈ e₉))))))),
    by unfold nrPassCost; omega, p, rfl, rfl, rfl, harc, hall, hNH, hLN,
    fun y => c₇.nmem (S + 3 * m + 4 * n + 1 + y), fun y hy => hD y hy, fun i hi => ?_,
    fun a h1 h2 => ?_, fun x hx => ?_, ?_, ?_, ?_⟩
  · rw [l₉ i hi, m₈, mem₇ _ (by rcases dG with h | h <;> omega),
      mem₇ (NH + i) (by rcases dN with h | h <;> omega), mem₇ (KY + i) (by rcases dK with h | h <;> omega)]
  · rw [k₉ a h2, m₈, mem₇ a h1]
  · rw [f₉ x (by omega), f₈ x (by omega), q₇ x (by omega) (by omega) (by omega)]
  · rw [rr₉, rr₈, rr₇, rr₆, rr₅, rr₄, rr₃, rr₂, rr₁]
  · rw [rm₉, rm₈, rm₇, rm₆, rm₅, rm₄, rm₃, rm₂, rm₁]
  · rw [o₉, o₈, o₇, o₆, o₅, o₄, o₃, o₂, o₁]

end BKMNW

end PlanarFlow
