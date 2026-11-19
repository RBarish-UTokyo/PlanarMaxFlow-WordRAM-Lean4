module

public import PlanarFlow.BKMNW.LinLoops
public import WordRAM.Machine.Iter
public import WordRAM.Machine.RealsToNat

/-!
# A store loop: `OUT[s i + o] := val i` for `i < n`

The workhorse of the array scans of `c2sP`: a `whileLtN a b body` whose body writes one word
`val i` at `Ob + s · i + o` (`0 < s`), increments the counter `a` and keeps the registers of a set
`keep`; the values may read anything not written by the loop (the body is given the memory of the
start off the written cells). **`lnStore`**: within `(B + 2) n + 2` steps every written cell holds
its value and every other cell is kept.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace BKMNW

namespace NcStep

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

variable {P : Input} {W : ℕ}

/-- **The store loop** (see the module docstring). -/
theorem lnStore {a b : ℕ} {body : Stmt} {Ob s o n B : ℕ} (hs : 0 < s) (val : ℕ → ℕ)
    (keep : ℕ → Prop) (c : Config) (hc : WordsBounded W c) (ha : c.nreg a = 0)
    (hb : c.nreg b = n) (hkb : keep b)
    (hbody : ∀ i (c' : Config), i < n → WordsBounded W c' → c'.nreg a = i →
      (∀ x, keep x → c'.nreg x = c.nreg x) →
      (∀ addr, (∀ j < n, addr ≠ Ob + s * j + o) → c'.nmem addr = c.nmem addr) →
      ∃ c'' k, Exec P W body c' c'' k ∧ k ≤ B ∧ c''.nreg a = i + 1 ∧
        (∀ x, keep x → c''.nreg x = c'.nreg x) ∧
        c''.nmem = upd c'.nmem (Ob + s * i + o) (val i) ∧ c''.rreg = c'.rreg ∧
        c''.rmem = c'.rmem ∧ c''.output = c'.output) :
    ∃ c' k, Exec P W (.whileLtN a b body) c c' k ∧ k ≤ (B + 2) * n + 2 ∧
      (∀ i < n, c'.nmem (Ob + s * i + o) = val i) ∧
      (∀ addr, (∀ j < n, addr ≠ Ob + s * j + o) → c'.nmem addr = c.nmem addr) ∧
      (∀ x, keep x → c'.nreg x = c.nreg x) ∧ c'.nreg a = n ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  let J : ℕ → Config → Prop := fun i c' =>
    (∀ x, keep x → c'.nreg x = c.nreg x) ∧ (∀ j < i, c'.nmem (Ob + s * j + o) = val j) ∧
    (∀ addr, (∀ j < i, addr ≠ Ob + s * j + o) → c'.nmem addr = c.nmem addr) ∧
    c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output
  obtain ⟨c', k, ex, hk, -, ha', j1, j2, j3, j4, j5, j6⟩ := lnRange (P := P) (a := a) (b := b)
    (body := body) J (B := B) c hc ha hb (Nat.zero_le n)
    ⟨fun _ _ => rfl, fun j hj => absurd hj (by omega), fun _ _ => rfl, rfl, rfl, rfl⟩
    (fun i c₁ hlo hi hw h1 h2 ⟨f₁, v₁, o₁, q1, q2, q3⟩ => by
      obtain ⟨c₂, k₂, e₂, hk₂, g1, f₂, m₂, r₂, rm₂, o₂⟩ := hbody i c₁ hi hw h1 f₁
        (fun addr ha' => by
          by_cases hlt : ∀ j < i, addr ≠ Ob + s * j + o
          · exact o₁ addr hlt
          · push Not at hlt
            obtain ⟨j, hj, rfl⟩ := hlt
            exact absurd rfl (ha' j (by omega)))
      have ub : ∀ j < i, Ob + s * j + o ≠ Ob + s * i + o := fun j hj h => by
        have : s * j = s * i := by omega
        have := Nat.eq_of_mul_eq_mul_left hs this; omega
      refine ⟨c₂, k₂, e₂, hk₂, g1, by rw [f₂ b hkb, f₁ b hkb, hb],
        ⟨fun x hx => by rw [f₂ x hx, f₁ x hx], fun j hj => ?_, fun addr ha' => ?_,
          by rw [r₂, q1], by rw [rm₂, q2], by rw [o₂, q3]⟩⟩
      · rw [m₂]
        rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
        · rw [upd_other _ _ _ (ub j hj)]; exact v₁ j hj
        · rw [upd_same]
      · rw [m₂, upd_other _ _ _ (ha' i (by omega))]
        exact o₁ addr fun j hj => ha' j (by omega))
  exact ⟨c', k, ex, hk, j2, j3, j1, ha', j4, j5, j6⟩

/-- **The registers a statement does not name are kept** (`Exec.liftSame` on itself and
determinism). -/
theorem Exec.nreg_frame {U : ℕ → Bool} {s : Stmt} {c c' : Config} {k : ℕ}
    (h : Exec P W s c c' k) (hs : s.regsOK U = true) (hr : s.noRand = true) :
    ∀ r, U r = false → c'.nreg r = c.nreg r := by
  obtain ⟨d', e', -, hK, -⟩ := h.liftSame hs hr le_rfl (d := c)
    ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩ h.wb_left
  obtain ⟨rfl, -⟩ := Exec.det h e'
  exact hK.nreg


end NcStep

end BKMNW

end PlanarFlow
