module

public import PlanarFlow.BKMNW.NcLoop

/-!
# The arithmetic passes of `c2sP`

* **`lnStoreIP`**: `lnStore` for in-place updates (the body sees the cells not yet written as at
  the start, so `OUT` may be one of the inputs);
* four loops over `t < m` (registers `9790` `t`, `9791 = 1`, `9792` `X` base, `9793` `Y` base,
  `9794` `OUT` base, `9795` `K`, `9796` `m`; scratch `9797`, `9798`):
  `axL`: `OUT[t] := X[t] + Y[t] ∸ K` (`F1 = FL + O − 2Z`, `FL := FL + PB − 2Z`);
  `sxL`: `OUT[t] := X[t] + K ∸ Y[t]` (`G' = FF + 2Z − FL`);
  `ngL`: `OUT[t] := K ∸ X[t]` (`FL := 2Z − FL` for `s2c`);
  `dfL`: `OUT[t] := X[t] ∸ X[t] · Y[t]` (the flags of `C ∖ C⁺` from `CF`, `MK`);
  each within `11 m + 4` steps (**`axL_exec`**, `sxL_exec`, `ngL_exec`, `dfL_exec`).
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace BKMNW

namespace NcStep

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

variable {P : Input} {W : ℕ}

/-- **The store loop for in-place updates.** -/
theorem lnStoreIP {a b : ℕ} {body : Stmt} {Ob n B : ℕ} (val : ℕ → ℕ)
    (keep : ℕ → Prop) (c : Config) (hc : WordsBounded W c) (ha : c.nreg a = 0)
    (hb : c.nreg b = n) (hkb : keep b)
    (hbody : ∀ i (c' : Config), i < n → WordsBounded W c' → c'.nreg a = i →
      (∀ x, keep x → c'.nreg x = c.nreg x) →
      (∀ addr, (∀ j < i, addr ≠ Ob + j) → c'.nmem addr = c.nmem addr) →
      ∃ c'' k, Exec P W body c' c'' k ∧ k ≤ B ∧ c''.nreg a = i + 1 ∧
        (∀ x, keep x → c''.nreg x = c'.nreg x) ∧
        c''.nmem = upd c'.nmem (Ob + i) (val i) ∧ c''.rreg = c'.rreg ∧
        c''.rmem = c'.rmem ∧ c''.output = c'.output) :
    ∃ c' k, Exec P W (.whileLtN a b body) c c' k ∧ k ≤ (B + 2) * n + 2 ∧
      (∀ i < n, c'.nmem (Ob + i) = val i) ∧
      (∀ addr, (addr < Ob ∨ Ob + n ≤ addr) → c'.nmem addr = c.nmem addr) ∧
      (∀ x, keep x → c'.nreg x = c.nreg x) ∧ c'.nreg a = n ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  let J : ℕ → Config → Prop := fun i c' =>
    (∀ x, keep x → c'.nreg x = c.nreg x) ∧ (∀ j < i, c'.nmem (Ob + j) = val j) ∧
    (∀ addr, (∀ j < i, addr ≠ Ob + j) → c'.nmem addr = c.nmem addr) ∧
    c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output
  obtain ⟨c', k, ex, hk, -, ha', j1, j2, j3, j4, j5, j6⟩ := lnRange (P := P) (a := a) (b := b)
    (body := body) J (B := B) c hc ha hb (Nat.zero_le n)
    ⟨fun _ _ => rfl, fun j hj => absurd hj (by omega), fun _ _ => rfl, rfl, rfl, rfl⟩
    (fun i c₁ hlo hi hw h1 h2 ⟨f₁, v₁, o₁, q1, q2, q3⟩ => by
      obtain ⟨c₂, k₂, e₂, hk₂, g1, f₂, m₂, r₂, rm₂, o₂⟩ := hbody i c₁ hi hw h1 f₁ o₁
      refine ⟨c₂, k₂, e₂, hk₂, g1, by rw [f₂ b hkb, f₁ b hkb, hb],
        ⟨fun x hx => by rw [f₂ x hx, f₁ x hx], fun j hj => ?_, fun addr ha' => ?_,
          by rw [r₂, q1], by rw [rm₂, q2], by rw [o₂, q3]⟩⟩
      · rw [m₂, upd_apply]
        rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
        · rw [iteF (by omega)]; exact v₁ j hj
        · rw [iteT rfl]
      · rw [m₂, upd_apply, iteF (ha' i (by omega))]
        exact o₁ addr fun j hj => ha' j (by omega))
  exact ⟨c', k, ex, hk, j2, fun addr h => j3 addr (fun j hj => by omega), j1, ha', j4, j5, j6⟩

/-! ### The loops -/

/-- `t := 0`, `1`. -/
def arI : Stmt := block [.constN 9790 0, .constN 9791 1]

/-- `OUT[t] := X[t] + Y[t] ∸ K`. -/
def axB : Stmt :=
  block [.addN 9797 9792 9790, .loadN 9797 9797, .addN 9798 9793 9790, .loadN 9798 9798,
    .addN 9797 9797 9798, .subN 9797 9797 9795, .addN 9798 9794 9790, .storeN 9798 9797,
    .addN 9790 9790 9791]

/-- `OUT[t] := X[t] + K ∸ Y[t]`. -/
def sxB : Stmt :=
  block [.addN 9797 9792 9790, .loadN 9797 9797, .addN 9797 9797 9795, .addN 9798 9793 9790,
    .loadN 9798 9798, .subN 9797 9797 9798, .addN 9798 9794 9790, .storeN 9798 9797,
    .addN 9790 9790 9791]

/-- `OUT[t] := K ∸ X[t]`. -/
def ngB : Stmt :=
  block [.addN 9797 9792 9790, .loadN 9797 9797, .subN 9797 9795 9797, .addN 9798 9794 9790,
    .storeN 9798 9797, .addN 9790 9790 9791]

/-- `OUT[t] := X[t] ∸ X[t] · Y[t]`. -/
def dfB : Stmt :=
  block [.addN 9797 9792 9790, .loadN 9797 9797, .addN 9798 9793 9790, .loadN 9798 9798,
    .mulN 9798 9797 9798, .subN 9797 9797 9798, .addN 9798 9794 9790, .storeN 9798 9797,
    .addN 9790 9790 9791]

def axL : Stmt := .seq arI (.whileLtN 9790 9796 axB)
def sxL : Stmt := .seq arI (.whileLtN 9790 9796 sxB)
def ngL : Stmt := .seq arI (.whileLtN 9790 9796 ngB)
def dfL : Stmt := .seq arI (.whileLtN 9790 9796 dfB)

/-- The registers written by the four loops. -/
def ArScr (r : ℕ) : Prop := r = 9790 ∨ r = 9791 ∨ r = 9797 ∨ r = 9798

theorem arI_exec (c : Config) (hc : WordsBounded W c) (hW : 1 ≤ W) :
    ∃ c' k, Exec P W arI c c' k ∧ k = 2 ∧ c'.nreg 9790 = 0 ∧ c'.nreg 9791 = 1 ∧
      (∀ r, r ≠ 9790 → r ≠ 9791 → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold arI
  exec_block
  all_goals try ((try config_simp); omega)
  refine ⟨rfl, ?_, ?_, fun r h1 h2 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  simp only [upd_apply]; split_ifs <;> omega

theorem axB_exec (c : Config) (hc : WordsBounded W c) {Xb Yb Ob K t : ℕ}
    (r90 : c.nreg 9790 = t) (r91 : c.nreg 9791 = 1) (r92 : c.nreg 9792 = Xb)
    (r93 : c.nreg 9793 = Yb) (r94 : c.nreg 9794 = Ob) (r95 : c.nreg 9795 = K)
    (w1 : Xb + t ≤ W) (w2 : Yb + t ≤ W) (w3 : Ob + t ≤ W) (w4 : t + 1 ≤ W)
    (w5 : c.nmem (Xb + t) + c.nmem (Yb + t) ≤ W) :
    ∃ c' k, Exec P W axB c c' k ∧ k = 9 ∧
      c'.nmem = upd c.nmem (Ob + t) (c.nmem (Xb + t) + c.nmem (Yb + t) - K) ∧
      c'.nreg 9790 = t + 1 ∧ (∀ r, r ≠ 9790 → r ≠ 9797 → r ≠ 9798 → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold axB
  exec_block
  all_goals try ((try config_simp); (try simp only [r90, r91, r92, r93, r94, r95]); omega)
  refine ⟨rfl, ?_, ?_, fun r h1 h2 h3 => ?_, rfl, rfl, rfl⟩
  all_goals config_simp
  · simp only [r90, r92, r93, r94, r95]
  · simp only [r90, r91]
  · simp only [upd_apply]; split_ifs <;> omega

theorem sxB_exec (c : Config) (hc : WordsBounded W c) {Xb Yb Ob K t : ℕ}
    (r90 : c.nreg 9790 = t) (r91 : c.nreg 9791 = 1) (r92 : c.nreg 9792 = Xb)
    (r93 : c.nreg 9793 = Yb) (r94 : c.nreg 9794 = Ob) (r95 : c.nreg 9795 = K)
    (w1 : Xb + t ≤ W) (w2 : Yb + t ≤ W) (w3 : Ob + t ≤ W) (w4 : t + 1 ≤ W)
    (w5 : c.nmem (Xb + t) + K ≤ W) :
    ∃ c' k, Exec P W sxB c c' k ∧ k = 9 ∧
      c'.nmem = upd c.nmem (Ob + t) (c.nmem (Xb + t) + K - c.nmem (Yb + t)) ∧
      c'.nreg 9790 = t + 1 ∧ (∀ r, r ≠ 9790 → r ≠ 9797 → r ≠ 9798 → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold sxB
  exec_block
  all_goals try ((try config_simp); (try simp only [r90, r91, r92, r93, r94, r95]); omega)
  refine ⟨rfl, ?_, ?_, fun r h1 h2 h3 => ?_, rfl, rfl, rfl⟩
  all_goals config_simp
  · simp only [r90, r92, r93, r94, r95]
  · simp only [r90, r91]
  · simp only [upd_apply]; split_ifs <;> omega

theorem ngB_exec (c : Config) (hc : WordsBounded W c) {Xb Ob K t : ℕ}
    (r90 : c.nreg 9790 = t) (r91 : c.nreg 9791 = 1) (r92 : c.nreg 9792 = Xb)
    (r94 : c.nreg 9794 = Ob) (r95 : c.nreg 9795 = K)
    (w1 : Xb + t ≤ W) (w3 : Ob + t ≤ W) (w4 : t + 1 ≤ W) :
    ∃ c' k, Exec P W ngB c c' k ∧ k = 6 ∧
      c'.nmem = upd c.nmem (Ob + t) (K - c.nmem (Xb + t)) ∧
      c'.nreg 9790 = t + 1 ∧ (∀ r, r ≠ 9790 → r ≠ 9797 → r ≠ 9798 → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hK : K ≤ W := by rw [← r95]; exact hc.1 _
  unfold ngB
  exec_block
  all_goals try ((try config_simp); (try simp only [r90, r91, r92, r94, r95]); omega)
  refine ⟨rfl, ?_, ?_, fun r h1 h2 h3 => ?_, rfl, rfl, rfl⟩
  all_goals config_simp
  · simp only [r90, r92, r94, r95]
  · simp only [r90, r91]
  · simp only [upd_apply]; split_ifs <;> omega

theorem dfB_exec (c : Config) (hc : WordsBounded W c) {Xb Yb Ob t : ℕ}
    (r90 : c.nreg 9790 = t) (r91 : c.nreg 9791 = 1) (r92 : c.nreg 9792 = Xb)
    (r93 : c.nreg 9793 = Yb) (r94 : c.nreg 9794 = Ob)
    (w1 : Xb + t ≤ W) (w2 : Yb + t ≤ W) (w3 : Ob + t ≤ W) (w4 : t + 1 ≤ W)
    (w5 : c.nmem (Xb + t) * c.nmem (Yb + t) ≤ W) :
    ∃ c' k, Exec P W dfB c c' k ∧ k = 9 ∧
      c'.nmem = upd c.nmem (Ob + t)
        (c.nmem (Xb + t) - c.nmem (Xb + t) * c.nmem (Yb + t)) ∧
      c'.nreg 9790 = t + 1 ∧ (∀ r, r ≠ 9790 → r ≠ 9797 → r ≠ 9798 → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hx : c.nmem (Xb + t) ≤ W := hc.2 _
  unfold dfB
  exec_block
  all_goals try ((try config_simp); (try simp only [r90, r91, r92, r93, r94]); omega)
  refine ⟨rfl, ?_, ?_, fun r h1 h2 h3 => ?_, rfl, rfl, rfl⟩
  all_goals config_simp
  · simp only [r90, r92, r93, r94]
  · simp only [r90, r91]
  · simp only [upd_apply]; split_ifs <;> omega

/-- The common hypotheses of the four loops: the registers and the layout. -/
structure ArIn (c : Config) (m Xb Yb Ob K : ℕ) : Prop where
  r92 : c.nreg 9792 = Xb
  r93 : c.nreg 9793 = Yb
  r94 : c.nreg 9794 = Ob
  r95 : c.nreg 9795 = K
  r96 : c.nreg 9796 = m
  wX : Xb + m ≤ W
  wY : Yb + m ≤ W
  wO : Ob + m ≤ W
  wm : m + 1 ≤ W
  /-- the inputs are not cells written earlier -/
  dX : ∀ t < m, ∀ j < t, Xb + t ≠ Ob + j
  dY : ∀ t < m, ∀ j < t, Yb + t ≠ Ob + j

/-- **The generic run of the four loops.** -/
theorem arLoop_exec {B' : Stmt} (val : (ℕ → ℕ) → ℕ → ℕ) (c : Config) (hc : WordsBounded W c)
    {m Xb Yb Ob K : ℕ} (hI : ArIn (W := W) c m Xb Yb Ob K)
    (hval : ∀ (mem mem' : ℕ → ℕ) t, mem' (Xb + t) = mem (Xb + t) →
      mem' (Yb + t) = mem (Yb + t) → val mem' t = val mem t)
    (hB : ∀ t (c' : Config), t < m → WordsBounded W c' → c'.nreg 9790 = t →
      c'.nreg 9791 = 1 → c'.nreg 9792 = Xb → c'.nreg 9793 = Yb → c'.nreg 9794 = Ob →
      c'.nreg 9795 = K →
      (c'.nmem (Xb + t) = c.nmem (Xb + t) ∧ c'.nmem (Yb + t) = c.nmem (Yb + t)) →
      ∃ c'' k, Exec P W B' c' c'' k ∧ k ≤ 9 ∧ c''.nmem = upd c'.nmem (Ob + t) (val c'.nmem t) ∧
        c''.nreg 9790 = t + 1 ∧ (∀ r, r ≠ 9790 → r ≠ 9797 → r ≠ 9798 → c''.nreg r = c'.nreg r) ∧
        c''.rreg = c'.rreg ∧ c''.rmem = c'.rmem ∧ c''.output = c'.output) :
    ∃ c' k, Exec P W (.seq arI (.whileLtN 9790 9796 B')) c c' k ∧ k ≤ 11 * m + 4 ∧
      (∀ t < m, c'.nmem (Ob + t) = val c.nmem t) ∧
      (∀ a, (a < Ob ∨ Ob + m ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, ¬ ArScr r → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c₀, k₀, e₀, hk₀, a90, a91, g₀, m₀, rr₀, rm₀, o₀⟩ :=
    arI_exec (P := P) c hc (by have := hI.wm; omega)
  have q : ∀ r, r ≠ 9790 → r ≠ 9791 → c₀.nreg r = c.nreg r := g₀
  obtain ⟨c₁, k₁, e₁, hk₁, v₁, f₁, g₁, a₁, rr₁, rm₁, o₁⟩ := lnStoreIP (P := P) (a := 9790)
    (b := 9796) (body := B') (Ob := Ob) (n := m) (B := 9) (val c.nmem)
    (fun r => r ≠ 9790 ∧ r ≠ 9797 ∧ r ≠ 9798) c₀ e₀.wb_right a90
    (by rw [q _ (by omega) (by omega), hI.r96]) (by omega)
    (fun t c' ht hw e90 hk hm => by
      have hx : c'.nmem (Xb + t) = c.nmem (Xb + t) := by
        rw [hm _ (hI.dX t ht), m₀]
      have hy : c'.nmem (Yb + t) = c.nmem (Yb + t) := by
        rw [hm _ (hI.dY t ht), m₀]
      obtain ⟨c'', k, ex, hk', m', b90, g', rr', rm', o'⟩ := hB t c' ht hw e90
        (by rw [hk _ ⟨by omega, by omega, by omega⟩, a91])
        (by rw [hk _ ⟨by omega, by omega, by omega⟩, q _ (by omega) (by omega), hI.r92])
        (by rw [hk _ ⟨by omega, by omega, by omega⟩, q _ (by omega) (by omega), hI.r93])
        (by rw [hk _ ⟨by omega, by omega, by omega⟩, q _ (by omega) (by omega), hI.r94])
        (by rw [hk _ ⟨by omega, by omega, by omega⟩, q _ (by omega) (by omega), hI.r95])
        ⟨hx, hy⟩
      refine ⟨c'', k, ex, by omega, b90, fun x hx' => g' x hx'.1 hx'.2.1 hx'.2.2, ?_, rr', rm',
        o'⟩
      rw [m', hval c.nmem c'.nmem t hx hy])
  refine ⟨c₁, k₀ + k₁, e₀.seq e₁, by omega, v₁, fun a ha => by rw [f₁ a ha, m₀],
    fun r hr => ?_, by rw [rr₁, rr₀], by rw [rm₁, rm₀], by rw [o₁, o₀]⟩
  unfold ArScr at hr
  rw [g₁ r ⟨by omega, by omega, by omega⟩, q r (by omega) (by omega)]

/-- **`OUT[t] := X[t] + Y[t] ∸ K`.** -/
theorem axL_exec (c : Config) (hc : WordsBounded W c) {m Xb Yb Ob K : ℕ}
    (hI : ArIn (W := W) c m Xb Yb Ob K)
    (w : ∀ t < m, c.nmem (Xb + t) + c.nmem (Yb + t) ≤ W) :
    ∃ c' k, Exec P W axL c c' k ∧ k ≤ 11 * m + 4 ∧
      (∀ t < m, c'.nmem (Ob + t) = c.nmem (Xb + t) + c.nmem (Yb + t) - K) ∧
      (∀ a, (a < Ob ∨ Ob + m ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, ¬ ArScr r → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output :=
  arLoop_exec (fun mem t => mem (Xb + t) + mem (Yb + t) - K) c hc hI
    (fun mem mem' t h1 h2 => by simp only [h1, h2])
    (fun t c' ht hw r90 r91 r92 r93 r94 r95 ⟨hx, hy⟩ => by
      obtain ⟨c'', k, ex, hk, h1, h2, h3, h4, h5, h6⟩ := axB_exec (P := P) c' hw r90 r91 r92 r93
        r94 r95 (by have := hI.wX; omega) (by have := hI.wY; omega) (by have := hI.wO; omega)
        (by have := hI.wm; omega) (by rw [hx, hy]; exact w t ht)
      exact ⟨c'', k, ex, by omega, h1, h2, h3, h4, h5, h6⟩)

/-- **`OUT[t] := X[t] + K ∸ Y[t]`.** -/
theorem sxL_exec (c : Config) (hc : WordsBounded W c) {m Xb Yb Ob K : ℕ}
    (hI : ArIn (W := W) c m Xb Yb Ob K) (w : ∀ t < m, c.nmem (Xb + t) + K ≤ W) :
    ∃ c' k, Exec P W sxL c c' k ∧ k ≤ 11 * m + 4 ∧
      (∀ t < m, c'.nmem (Ob + t) = c.nmem (Xb + t) + K - c.nmem (Yb + t)) ∧
      (∀ a, (a < Ob ∨ Ob + m ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, ¬ ArScr r → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output :=
  arLoop_exec (fun mem t => mem (Xb + t) + K - mem (Yb + t)) c hc hI
    (fun mem mem' t h1 h2 => by simp only [h1, h2])
    (fun t c' ht hw r90 r91 r92 r93 r94 r95 ⟨hx, hy⟩ => by
      obtain ⟨c'', k, ex, hk, h1, h2, h3, h4, h5, h6⟩ := sxB_exec (P := P) c' hw r90 r91 r92 r93
        r94 r95 (by have := hI.wX; omega) (by have := hI.wY; omega) (by have := hI.wO; omega)
        (by have := hI.wm; omega) (by rw [hx]; exact w t ht)
      exact ⟨c'', k, ex, by omega, h1, h2, h3, h4, h5, h6⟩)

/-- **`OUT[t] := K ∸ X[t]`.** -/
theorem ngL_exec (c : Config) (hc : WordsBounded W c) {m Xb Yb Ob K : ℕ}
    (hI : ArIn (W := W) c m Xb Yb Ob K) :
    ∃ c' k, Exec P W ngL c c' k ∧ k ≤ 11 * m + 4 ∧
      (∀ t < m, c'.nmem (Ob + t) = K - c.nmem (Xb + t)) ∧
      (∀ a, (a < Ob ∨ Ob + m ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, ¬ ArScr r → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output :=
  arLoop_exec (fun mem t => K - mem (Xb + t)) c hc hI
    (fun mem mem' t h1 h2 => by simp only [h1])
    (fun t c' ht hw r90 r91 r92 r93 r94 r95 ⟨hx, hy⟩ => by
      obtain ⟨c'', k, ex, hk, h1, h2, h3, h4, h5, h6⟩ := ngB_exec (P := P) c' hw r90 r91 r92 r94
        r95 (by have := hI.wX; omega) (by have := hI.wO; omega) (by have := hI.wm; omega)
      exact ⟨c'', k, ex, by omega, h1, h2, h3, h4, h5, h6⟩)

/-- **`OUT[t] := X[t] ∸ X[t] · Y[t]`.** -/
theorem dfL_exec (c : Config) (hc : WordsBounded W c) {m Xb Yb Ob K : ℕ}
    (hI : ArIn (W := W) c m Xb Yb Ob K) (w : ∀ t < m, c.nmem (Xb + t) * c.nmem (Yb + t) ≤ W) :
    ∃ c' k, Exec P W dfL c c' k ∧ k ≤ 11 * m + 4 ∧
      (∀ t < m, c'.nmem (Ob + t) = c.nmem (Xb + t) - c.nmem (Xb + t) * c.nmem (Yb + t)) ∧
      (∀ a, (a < Ob ∨ Ob + m ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, ¬ ArScr r → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output :=
  arLoop_exec (fun mem t => mem (Xb + t) - mem (Xb + t) * mem (Yb + t)) c hc hI
    (fun mem mem' t h1 h2 => by simp only [h1, h2])
    (fun t c' ht hw r90 r91 r92 r93 r94 r95 ⟨hx, hy⟩ => by
      obtain ⟨c'', k, ex, hk, h1, h2, h3, h4, h5, h6⟩ := dfB_exec (P := P) c' hw r90 r91 r92 r93
        r94 (by have := hI.wX; omega) (by have := hI.wY; omega) (by have := hI.wO; omega)
        (by have := hI.wm; omega) (by rw [hx, hy]; exact w t ht)
      exact ⟨c'', k, ex, by omega, h1, h2, h3, h4, h5, h6⟩)

end NcStep

end BKMNW

end PlanarFlow
