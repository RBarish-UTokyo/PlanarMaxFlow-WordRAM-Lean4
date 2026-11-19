module

public import PlanarFlow.NegSSSP.Enc.HoistRun

/-!
# Parameter programs: polynomial values written into registers

The parameters of the fixed programs (`feVL p`, `hnVL …`) are polynomials in a few primary
values (the sizes and bases of the instance). A parameter is given as a list of terms
`c · m` (`c ≥ 1`, `m` a monomial: `1`, a register, or the product of two registers) minus a
constant `d` (`hpSum f ts - d`, truncated subtraction as on the machine):

* `hpM`, `hpM.ev`, `hpSum`;
* `hpL dst t ts` (`dst += c · m` for each term, scratch `t`, `t + 1`), `hpTC dst t ts d`
  (`dst := Σ c · m - d`), **`hpTC_exec`**: within `4 #ts + 3` steps, `dst` holds the value
  computed from the registers of the start, every other register but `t`, `t + 1` and all memory
  kept, provided the registers read are not `dst`, `t`, `t + 1`, `1 ≤ c ≤ W`, `d ≤ W` and the sum
  is `≤ W`;
* `hpProg PB t es` (the `j`-th parameter into `PB + j`), **`hpProg_exec`**: all parameters
  computed from the start's registers (none of which lies in `[PB, PB + #es)` or is `t`, `t + 1`),
  within `Σ (4 #tsⱼ + 3)` steps.
-/

@[expose] public section

namespace PlanarFlow

namespace NegSSSP

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt

/-- A monomial: `1`, a register, or the product of two registers. -/
inductive hpM where
  | one
  | v (r : ℕ)
  | vv (r s : ℕ)

/-- The value of a monomial for the register values `f`. -/
def hpM.ev (f : ℕ → ℕ) : hpM → ℕ
  | .one => 1
  | .v r => f r
  | .vv r s => f r * f s

/-- The registers a monomial reads avoid `x`. -/
def hpM.avoid (x : ℕ) : hpM → Prop
  | .one => True
  | .v r => r ≠ x
  | .vv r s => r ≠ x ∧ s ≠ x

/-- The code of a monomial into the register `t`. -/
def hpM.code (t : ℕ) : hpM → Stmt
  | .one => .instr (.constN t 1)
  | .v r => .instr (.copyN t r)
  | .vv r s => .instr (.mulN t r s)

/-- `Σ c · m`. -/
def hpSum (f : ℕ → ℕ) (ts : List (ℕ × hpM)) : ℕ := (ts.map fun x => x.1 * x.2.ev f).sum

/-- `dst += c · m` for each term. -/
def hpL (dst t : ℕ) : List (ℕ × hpM) → Stmt
  | [] => .skip
  | (c, m) :: l => .seq (m.code t) <| .seq (.instr (.constN (t + 1) c)) <|
      .seq (.instr (.mulN t t (t + 1))) <| .seq (.instr (.addN dst dst t)) (hpL dst t l)

/-- `dst := Σ c · m - d`. -/
def hpTC (dst t : ℕ) (ts : List (ℕ × hpM)) (d : ℕ) : Stmt :=
  .seq (.instr (.constN dst 0)) <| .seq (hpL dst t ts) <|
    .seq (.instr (.constN (t + 1) d)) (.instr (.subN dst dst (t + 1)))

/-- The conditions on a parameter: its registers avoid `dst`, `t`, `t + 1`, `1 ≤ c ≤ W`. -/
def hpOK (W dst t : ℕ) (ts : List (ℕ × hpM)) : Prop :=
  ∀ x ∈ ts, 1 ≤ x.1 ∧ x.1 ≤ W ∧ x.2.avoid dst ∧ x.2.avoid t ∧ x.2.avoid (t + 1)

theorem hpM_ev_frame {f g : ℕ → ℕ} {m : hpM} {x y z : ℕ} (hx : m.avoid x) (hy : m.avoid y)
    (hz : m.avoid z) (h : ∀ r, r ≠ x → r ≠ y → r ≠ z → g r = f r) : m.ev g = m.ev f := by
  cases m with
  | one => rfl
  | v r => exact h r hx hy hz
  | vv r s => simp only [hpM.ev, h r hx.1 hy.1 hz.1, h s hx.2 hy.2 hz.2]

theorem hpL_exec {I : Input} {W dst t : ℕ} (ts : List (ℕ × hpM)) (hok : hpOK W dst t ts)
    (hdt : dst ≠ t) (hdt' : dst ≠ t + 1) (c : Config) (hc : WordsBounded W c)
    (hW : c.nreg dst + hpSum c.nreg ts ≤ W) :
    ∃ c', Exec I W (hpL dst t ts) c c' (4 * ts.length) ∧
      c'.nreg dst = c.nreg dst + hpSum c.nreg ts ∧
      (∀ r, r ≠ dst → r ≠ t → r ≠ t + 1 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  induction ts generalizing c with
  | nil => exact ⟨c, .skip hc, by simp [hpSum], fun _ _ _ _ => rfl, rfl, rfl, rfl, rfl⟩
  | cons x l ih =>
    obtain ⟨cc, m⟩ := x
    obtain ⟨h1, h2, ha, hb, hd⟩ := hok (cc, m) (by simp)
    have hok' : hpOK W dst t l := fun y hy => hok y (by simp [hy])
    have hsum : hpSum c.nreg ((cc, m) :: l) = cc * m.ev c.nreg + hpSum c.nreg l := by
      simp [hpSum]
    rw [hsum] at hW
    have hmW : m.ev c.nreg ≤ W := by
      have : m.ev c.nreg ≤ cc * m.ev c.nreg := Nat.le_mul_of_pos_left _ h1
      omega
    -- the monomial into `t`
    have hm1 : ∃ c₁, Exec I W (m.code t) c c₁ 1 ∧ c₁.nreg t = m.ev c.nreg ∧
        (∀ r, r ≠ t → c₁.nreg r = c.nreg r) ∧ c₁.nmem = c.nmem ∧ c₁.rreg = c.rreg ∧
        c₁.rmem = c.rmem ∧ c₁.output = c.output := by
      cases m with
      | one => exact ⟨_, Exec.constN hc t 1 (by omega), by simp [hpM.ev],
          fun r h => upd_other _ _ _ h, rfl, rfl, rfl, rfl⟩
      | v r => exact ⟨_, Exec.copyN hc t r, by simp [hpM.ev], fun r h => upd_other _ _ _ h,
          rfl, rfl, rfl, rfl⟩
      | vv r s => exact ⟨_, Exec.mulN hc t r s (by simpa [hpM.ev] using hmW), by simp [hpM.ev],
          fun r h => upd_other _ _ _ h, rfl, rfl, rfl, rfl⟩
    obtain ⟨c₁, e₁, a1, b1, m1, r1, rm1, o1⟩ := hm1
    have e₂ := Exec.constN (P := I) e₁.wb_right (t + 1) cc h2
    set c₂ := { c₁ with nreg := upd c₁.nreg (t + 1) cc } with hc₂
    have a2 : c₂.nreg t = m.ev c.nreg := by
      show upd c₁.nreg (t + 1) cc t = _; rw [upd_other _ _ _ (by omega), a1]
    have b2 : c₂.nreg (t + 1) = cc := upd_same _ _ _
    have f2 : ∀ r, r ≠ t + 1 → c₂.nreg r = c₁.nreg r := fun r h => upd_other _ _ _ h
    have e₃ := Exec.mulN (P := I) e₂.wb_right t t (t + 1) (by rw [a2, b2, Nat.mul_comm]; omega)
    set c₃ := { c₂ with nreg := upd c₂.nreg t (c₂.nreg t * c₂.nreg (t + 1)) } with hc₃
    have a3 : c₃.nreg t = cc * m.ev c.nreg := by
      show upd c₂.nreg t _ t = _; rw [upd_same, a2, b2, Nat.mul_comm]
    have f3 : ∀ r, r ≠ t → c₃.nreg r = c₂.nreg r := fun r h => upd_other _ _ _ h
    have hd3 : c₃.nreg dst = c.nreg dst := by rw [f3 _ hdt, f2 _ hdt', b1 _ hdt]
    have e₄ := Exec.addN (P := I) e₃.wb_right dst dst t (by rw [hd3, a3]; omega)
    set c₄ := { c₃ with nreg := upd c₃.nreg dst (c₃.nreg dst + c₃.nreg t) } with hc₄
    have hd₄ : c₄.nreg dst = c.nreg dst + cc * m.ev c.nreg := by
      show upd c₃.nreg dst _ dst = _; rw [upd_same, hd3, a3]
    have hfr : ∀ r, r ≠ dst → r ≠ t → r ≠ t + 1 → c₄.nreg r = c.nreg r := fun r a b d => by
      show upd c₃.nreg dst _ r = _; rw [upd_other _ _ _ a, f3 r b, f2 r d, b1 r b]
    have m4 : c₄.nmem = c.nmem := m1
    have r4 : c₄.rreg = c.rreg := r1
    have rm4 : c₄.rmem = c.rmem := rm1
    have o4 : c₄.output = c.output := o1
    have hsl : hpSum c₄.nreg l = hpSum c.nreg l := by
      unfold hpSum; congr 1
      apply List.map_congr_left
      intro y hy
      obtain ⟨-, -, a, b, d⟩ := hok' y hy
      rw [hpM_ev_frame a b d hfr]
    obtain ⟨c', e', v', f', m', r', rm', o'⟩ := ih hok' c₄ e₄.wb_right (by rw [hd₄, hsl]; omega)
    refine ⟨c', (Exec.seq e₁ (Exec.seq e₂ (Exec.seq e₃ (Exec.seq e₄ e')))).cast
      (by simp only [List.length_cons]; ring),
      by rw [v', hd₄, hsl, hsum]; ring, fun r a b d => by rw [f' r a b d, hfr r a b d],
      by rw [m', m4], by rw [r', r4], by rw [rm', rm4], by rw [o', o4]⟩

/-- **One parameter on the machine** (see the module docstring). -/
theorem hpTC_exec {I : Input} {W dst t : ℕ} (ts : List (ℕ × hpM)) (d : ℕ) (hok : hpOK W dst t ts)
    (hdt : dst ≠ t) (hdt' : dst ≠ t + 1) (c : Config) (hc : WordsBounded W c)
    (hW : hpSum c.nreg ts ≤ W) (hd : d ≤ W) :
    ∃ c', Exec I W (hpTC dst t ts d) c c' (4 * ts.length + 3) ∧
      c'.nreg dst = hpSum c.nreg ts - d ∧
      (∀ r, r ≠ dst → r ≠ t → r ≠ t + 1 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have e₀ := Exec.constN (P := I) hc dst 0 (Nat.zero_le _)
  set c₀ := { c with nreg := upd c.nreg dst 0 } with hc₀
  have f₀ : ∀ r, r ≠ dst → c₀.nreg r = c.nreg r := fun r h => upd_other _ _ _ h
  have hs₀ : hpSum c₀.nreg ts = hpSum c.nreg ts := by
    unfold hpSum; congr 1
    apply List.map_congr_left
    intro y hy
    obtain ⟨-, -, a, b, d⟩ := hok y hy
    rw [hpM_ev_frame a b d (fun r h _ _ => f₀ r h)]
  obtain ⟨c₁, e₁, v₁, f₁, m₁, r₁, rm₁, o₁⟩ := hpL_exec (I := I) ts hok hdt hdt' c₀ e₀.wb_right
    (by rw [hs₀]; simp [hc₀]; exact hW)
  have e₂ := Exec.constN (P := I) e₁.wb_right (t + 1) d hd
  have e₃ := Exec.subN (P := I) e₂.wb_right dst dst (t + 1)
  refine ⟨_, (Exec.seq e₀ (Exec.seq e₁ (Exec.seq e₂ e₃))).cast (by omega), ?_,
    fun r a b dd => ?_, by rw [hc₀] at m₁; simpa using m₁, by rw [hc₀] at r₁; simpa using r₁,
    by rw [hc₀] at rm₁; simpa using rm₁, by rw [hc₀] at o₁; simpa using o₁⟩
  · simp only [upd_same, upd_other _ _ _ hdt']
    rw [v₁, hs₀]; simp [hc₀]
  · simp only [upd_other _ _ _ a, upd_other _ _ _ dd]
    rw [f₁ r a b dd, f₀ r a]

/-- **The parameters `es` into `PB + j`.** -/
def hpProg (PB t : ℕ) : List (List (ℕ × hpM) × ℕ) → Stmt
  | [] => .skip
  | e :: es => .seq (hpTC PB t e.1 e.2) (hpProg (PB + 1) t es)

/-- The cost of `hpProg`. -/
def hpCost : List (List (ℕ × hpM) × ℕ) → ℕ
  | [] => 0
  | e :: es => 4 * e.1.length + 3 + hpCost es

/-- The conditions on a list of parameters into `[PB, PB + #es)`: every register read is outside
that range and is not `t`, `t + 1`; `t + 1 < PB` or `PB + #es ≤ t`; coefficients in `[1, W]`. -/
def hpProgOK (W PB t : ℕ) (es : List (List (ℕ × hpM) × ℕ)) : Prop :=
  (t + 1 < PB ∨ PB + es.length ≤ t) ∧ ∀ e ∈ es, e.2 ≤ W ∧ ∀ x ∈ e.1, 1 ≤ x.1 ∧ x.1 ≤ W ∧
    (∀ y, PB ≤ y → y < PB + es.length → x.2.avoid y) ∧ x.2.avoid t ∧ x.2.avoid (t + 1)

/-- **The parameter program** (see the module docstring). -/
theorem hpProg_exec {I : Input} {W t : ℕ} (es : List (List (ℕ × hpM) × ℕ)) (PB : ℕ)
    (hok : hpProgOK W PB t es) (c : Config) (hc : WordsBounded W c)
    (hW : ∀ e ∈ es, hpSum c.nreg e.1 ≤ W) :
    ∃ c', Exec I W (hpProg PB t es) c c' (hpCost es) ∧
      (∀ j < es.length, c'.nreg (PB + j) = hpSum c.nreg (es.getD j ([], 0)).1 -
        (es.getD j ([], 0)).2) ∧
      (∀ r, (r < PB ∨ PB + es.length ≤ r) → r ≠ t → r ≠ t + 1 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  induction es generalizing PB c with
  | nil => exact ⟨c, .skip hc, fun j hj => by simp at hj, fun _ _ _ _ => rfl, rfl, rfl, rfl, rfl⟩
  | cons e es ih =>
    obtain ⟨hpt, hes⟩ := hok
    simp only [List.length_cons] at hpt
    obtain ⟨hd, hts⟩ := hes e (by simp)
    have hok₁ : hpOK W PB t e.1 := fun x hx => by
      obtain ⟨a, b, c', d, f⟩ := hts x hx
      exact ⟨a, b, c' PB le_rfl (by simp), d, f⟩
    obtain ⟨c₁, e₁, v₁, f₁, m₁, r₁, rm₁, o₁⟩ := hpTC_exec (I := I) e.1 e.2 hok₁ (by omega)
      (by omega) c hc (hW e (by simp)) hd
    have hfr : ∀ r, r ≠ PB → r ≠ t → r ≠ t + 1 → c₁.nreg r = c.nreg r := f₁
    have hsame : ∀ e' ∈ es, hpSum c₁.nreg e'.1 = hpSum c.nreg e'.1 := fun e' he' => by
      obtain ⟨-, hts'⟩ := hes e' (by simp [he'])
      unfold hpSum; congr 1
      apply List.map_congr_left
      intro y hy
      obtain ⟨-, -, a, b, d⟩ := hts' y hy
      rw [hpM_ev_frame (a PB le_rfl (by simp)) b d hfr]
    have hok' : hpProgOK W (PB + 1) t es := by
      refine ⟨by omega, fun e' he' => ?_⟩
      obtain ⟨hd', hts'⟩ := hes e' (by simp [he'])
      refine ⟨hd', fun x hx => ?_⟩
      obtain ⟨a, b, c', d, f⟩ := hts' x hx
      exact ⟨a, b, fun y h1 h2 => c' y (by omega) (by simp only [List.length_cons]; omega), d, f⟩
    obtain ⟨c', e', v', f', m', r', rm', o'⟩ := ih (PB + 1) hok' c₁ e₁.wb_right
      (fun e' he' => by rw [hsame e' he']; exact hW e' (by simp [he']))
    refine ⟨c', (Exec.seq e₁ e').cast (by simp [hpCost]), fun j hj => ?_,
      fun r h1 h2 h3 => ?_, by rw [m', m₁], by rw [r', r₁], by rw [rm', rm₁], by rw [o', o₁]⟩
    · rcases j with _ | j
      · show c'.nreg PB = _
        rw [f' PB (Or.inl (by omega)) (by omega) (by omega), v₁]; rfl
      · simp only [List.length_cons] at hj
        have := v' j (by omega)
        have hm : es.getD j ([], 0) ∈ es := by
          rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _
        rw [show PB + (j + 1) = PB + 1 + j by omega, this, hsame _ hm]
        rfl
    · rw [f' r (by simp only [List.length_cons] at h1; omega) h2 h3,
        hfr r (by simp only [List.length_cons] at h1; omega) h2 h3]

end NegSSSP

end PlanarFlow
