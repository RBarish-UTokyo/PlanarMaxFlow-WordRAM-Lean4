module

public import PlanarFlow.BKMNW.EncScan
public import PlanarFlow.BKMNW.BfsProg

/-!
# The orbits of an index permutation, numbered contiguously, on the machine

For an index permutation `P` of `[0, m)` with inverse `PI` (arrays), the orbits are the connected
components of the graph `u — P[u]`, `u — PI[u]` (degree `2`, symmetric). The program builds its
CSR form (`c2Prog`: `OFF[u] = 2u`, `ADJ[2u] = P[u]`, `ADJ[2u+1] = PI[u]`), labels the components
by breadth-first search (`bfProg`) and renumbers the labels contiguously from `0` (`rkProg`).

* `pAdj p pi m u v` (`u < m ∧ (v = p u ∨ v = pi u)`), `PermArr` (values `< m`, mutually inverse).
* `c2Body`, **`c2Prog`**, `c2Body_exec` (12 steps), **`c2Prog_exec`** (`14 m + 7` steps);
  `bfAdj_c2` (the CSR adjacency is `pAdj`), `bfIn_c2`.
* **`orbProg`** (`orbSet ; c2Prog ; bfProg ; rkProg`), **`orbProg_exec`**: inputs `4650 = m`,
  `4651 = Pb`, `4652 = PIb`, `4653 = Sb` (scratch of `6 m + 3` words, label and table parts
  zero), `4654 = OUTb`; within `85 m + 37` steps `OUT[i] = OUT[j] ↔ ReflTransGen (pAdj P PI m)
  i j`, `OUT[j] < r4616`, every number `< r4616` is some `OUT[j]`.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace PlanarFlow

namespace BKMNW

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs Relation

/-- The adjacency of the orbit graph of an index permutation. -/
def pAdj (p pi : ℕ → ℕ) (m u v : ℕ) : Prop := u < m ∧ (v = p u ∨ v = pi u)

/-- Two arrays of `[0, m)` inverse to each other. -/
structure PermArr (p pi : ℕ → ℕ) (m : ℕ) : Prop where
  plt : ∀ u < m, p u < m
  pilt : ∀ u < m, pi u < m
  left : ∀ u < m, pi (p u) = u
  right : ∀ u < m, p (pi u) = u

lemma pAdj_symm {p pi : ℕ → ℕ} {m : ℕ} (h : PermArr p pi m) {u v : ℕ} (huv : pAdj p pi m u v) :
    pAdj p pi m v u := by
  obtain ⟨hu, rfl | rfl⟩ := huv
  · exact ⟨h.plt u hu, Or.inr (h.left u hu).symm⟩
  · exact ⟨h.pilt u hu, Or.inl (h.right u hu).symm⟩

/-- `OFF[u] := 2u`, `ADJ[2u] := P[u]`, `ADJ[2u+1] := PI[u]`. -/
def c2Body : Stmt :=
  block [.addN 4647 4646 4646, .addN 4648 4643 4646, .storeN 4648 4647, .addN 4648 4641 4646,
    .loadN 4648 4648, .addN 4649 4644 4647, .storeN 4649 4648, .addN 4648 4642 4646,
    .loadN 4648 4648, .addN 4649 4649 4645, .storeN 4649 4648, .addN 4646 4646 4645]

/-- **The CSR form of the orbit graph on the machine** (and `OFF[m] := 2m`). -/
def c2Prog : Stmt :=
  .seq (block [.constN 4645 1, .constN 4646 0])
    (.seq (.whileLtN 4646 4640 c2Body)
      (block [.addN 4647 4640 4640, .addN 4648 4643 4640, .storeN 4648 4647]))

section C2

variable {P : Input} {W : ℕ}

theorem c2Body_exec (c : Config) (hc : WordsBounded W c) {Pb PIb OFFb ADJb u p q : ℕ}
    (r1 : c.nreg 4641 = Pb) (r2 : c.nreg 4642 = PIb) (r3 : c.nreg 4643 = OFFb)
    (r4 : c.nreg 4644 = ADJb) (r5 : c.nreg 4645 = 1) (r6 : c.nreg 4646 = u)
    (hp : c.nmem (Pb + u) = p) (hq : c.nmem (PIb + u) = q)
    (d1 : Pb + u ≠ OFFb + u) (d2 : PIb + u ≠ OFFb + u) (d3 : PIb + u ≠ ADJb + 2 * u)
    (w1 : OFFb + u ≤ W) (w2 : ADJb + 2 * u + 1 ≤ W) (w3 : Pb + u ≤ W) (w4 : PIb + u ≤ W)
    (w5 : 2 * u + 1 ≤ W) :
    ∃ c' k, Exec P W c2Body c c' k ∧ k = 12 ∧ c'.nreg 4646 = u + 1 ∧
      c'.nmem = upd (upd (upd c.nmem (OFFb + u) (2 * u)) (ADJb + 2 * u) p) (ADJb + 2 * u + 1) q ∧
      (∀ x, (x < 4646 ∨ 4649 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hpW : p ≤ W := hp ▸ hc.2 _
  have hqW : q ≤ W := hq ▸ hc.2 _
  unfold c2Body
  exec_block
  all_goals try (config_simp; simp only [r1, r2, r3, r4, r5, r6, upd_apply]; split_ifs <;> omega)
  all_goals try (config_simp; simp only [r1, r2, r3, r4, r5, r6]; omega)
  refine ⟨rfl, ?_, ?_, fun x hx => ?_, rfl, rfl, rfl⟩
  · config_simp; simp only [r5, r6]
  · config_simp
    funext a
    simp only [r1, r2, r3, r4, r5, r6, upd_apply]
    split_ifs <;> omega
  · config_simp; simp only [upd_apply]; split_ifs <;> omega

/-- **The CSR form**: with `P[u] = nmem (Pb + u)`, `PI[u] = nmem (PIb + u)` (`u < m`) outside
`OFF = [OFFb, OFFb + m + 1)` and `ADJ = [ADJb, ADJb + 2 m)`: within `14 m + 7` steps
`OFF[u] = 2u` (`u ≤ m`), `ADJ[2u] = P[u]`, `ADJ[2u+1] = PI[u]` (`u < m`); memory outside `OFF`
and `ADJ` and registers outside `4645 … 4649` kept. -/
theorem c2Prog_exec (c : Config) (hc : WordsBounded W c) {m Pb PIb OFFb ADJb : ℕ}
    (r0 : c.nreg 4640 = m) (r1 : c.nreg 4641 = Pb) (r2 : c.nreg 4642 = PIb)
    (r3 : c.nreg 4643 = OFFb) (r4 : c.nreg 4644 = ADJb) (l1 : OFFb + m + 1 ≤ ADJb)
    (dP : ∀ u < m, ¬ (OFFb ≤ Pb + u ∧ Pb + u < ADJb + 2 * m))
    (dPI : ∀ u < m, ¬ (OFFb ≤ PIb + u ∧ PIb + u < ADJb + 2 * m))
    (w1 : ADJb + 2 * m + 1 ≤ W) (w2 : Pb + m ≤ W) (w3 : PIb + m ≤ W) :
    ∃ c' k, Exec P W c2Prog c c' k ∧ k ≤ 14 * m + 7 ∧
      (∀ u ≤ m, c'.nmem (OFFb + u) = 2 * u) ∧
      (∀ u < m, c'.nmem (ADJb + 2 * u) = c.nmem (Pb + u)) ∧
      (∀ u < m, c'.nmem (ADJb + 2 * u + 1) = c.nmem (PIb + u)) ∧
      (∀ a, ¬ (OFFb ≤ a ∧ a < ADJb + 2 * m) → c'.nmem a = c.nmem a) ∧
      (∀ x, (x < 4645 ∨ 4649 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold c2Prog
  obtain ⟨c₁, k₁, e₁, hk₁, g5, g6, gn₁, gm₁, gr₁, grm₁, go₁⟩ : ∃ c₁ k₁,
      Exec P W (block [.constN 4645 1, .constN 4646 0]) c c₁ k₁ ∧ k₁ = 2 ∧
      c₁.nreg 4645 = 1 ∧ c₁.nreg 4646 = 0 ∧
      (∀ x, x ≠ 4645 → x ≠ 4646 → c₁.nreg x = c.nreg x) ∧ c₁.nmem = c.nmem ∧
      c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    exec_block
    all_goals try ((try config_simp); omega)
    refine ⟨rfl, ?_, ?_, fun x a b => ?_, rfl, rfl, rfl, rfl⟩
    · config_simp
    · config_simp
    · config_simp; simp only [upd_apply]; split_ifs <;> omega
  have hw₁ := e₁.wb_right
  have q : ∀ x, x ≠ 4645 → x ≠ 4646 → c₁.nreg x = c.nreg x := gn₁
  set m₀ := c.nmem with hm₀
  let J : ℕ → Config → Prop := fun i c' =>
    (∀ x, (x < 4646 ∨ 4649 < x) → c'.nreg x = c₁.nreg x) ∧
    (∀ u < i, c'.nmem (OFFb + u) = 2 * u) ∧
    (∀ u < i, c'.nmem (ADJb + 2 * u) = m₀ (Pb + u)) ∧
    (∀ u < i, c'.nmem (ADJb + 2 * u + 1) = m₀ (PIb + u)) ∧
    (∀ a, ¬ (OFFb ≤ a ∧ a < OFFb + i) → ¬ (ADJb ≤ a ∧ a < ADJb + 2 * i) → c'.nmem a = m₀ a) ∧
    c'.rreg = c₁.rreg ∧ c'.rmem = c₁.rmem ∧ c'.output = c₁.output
  obtain ⟨c₂, k₂, e₂, hk₂, hw₂, h75, j1, jo, ja, jb, j3, j4, j5, j6⟩ := tgRange (P := P)
    (a := 4646) (b := 4640) (body := c2Body) J (B := 12) c₁ hw₁ g6
    (by rw [q _ (by omega) (by omega), r0])
    (Nat.zero_le m) ⟨fun _ _ => rfl, fun u hu => absurd hu (by omega),
      fun u hu => absurd hu (by omega), fun u hu => absurd hu (by omega),
      fun a _ _ => by rw [gm₁], rfl, rfl, rfl⟩
    (fun i c' hlo hhi hw h75 h70 ⟨j1, jo, ja, jb, j3, j4, j5, j6⟩ => by
      have f : ∀ x, (x < 4646 ∨ 4649 < x) → c'.nreg x = c₁.nreg x := j1
      have e1 : c'.nmem (Pb + i) = m₀ (Pb + i) :=
        j3 _ (fun h => dP i hhi ⟨h.1, by omega⟩) (fun h => dP i hhi ⟨by omega, by omega⟩)
      have e2 : c'.nmem (PIb + i) = m₀ (PIb + i) :=
        j3 _ (fun h => dPI i hhi ⟨h.1, by omega⟩) (fun h => dPI i hhi ⟨by omega, by omega⟩)
      obtain ⟨c'', t, ex, ht, h75', hm', hn', hr', hrm', ho'⟩ := c2Body_exec (P := P) c' hw
        (by rw [f _ (by omega), q _ (by omega) (by omega), r1])
        (by rw [f _ (by omega), q _ (by omega) (by omega), r2])
        (by rw [f _ (by omega), q _ (by omega) (by omega), r3])
        (by rw [f _ (by omega), q _ (by omega) (by omega), r4])
        (by rw [f _ (by omega), g5]) h75 e1 e2
        (fun h => dP i hhi ⟨by omega, by omega⟩) (fun h => dPI i hhi ⟨by omega, by omega⟩)
        (fun h => dPI i hhi ⟨by omega, by omega⟩) (by omega) (by omega) (by omega) (by omega)
        (by omega)
      refine ⟨c'', t, ex, ht.le, h75', by rw [hn' _ (by omega)]; exact h70,
        fun x hx => by rw [hn' x hx, f x hx], fun u hu => ?_, fun u hu => ?_, fun u hu => ?_,
        fun a ha hb => ?_, by rw [hr', j4], by rw [hrm', j5], by rw [ho', j6]⟩
      · rw [hm', upd_other _ _ _ (by omega), upd_other _ _ _ (by omega)]
        rcases Nat.lt_succ_iff_lt_or_eq.1 hu with hu | rfl
        · rw [upd_other _ _ _ (by omega)]; exact jo u hu
        · rw [upd_same]
      · rw [hm', upd_other _ _ _ (by omega)]
        rcases Nat.lt_succ_iff_lt_or_eq.1 hu with hu | rfl
        · rw [upd_other _ _ _ (by omega), upd_other _ _ _ (by omega)]; exact ja u hu
        · rw [upd_same]
      · rw [hm']
        rcases Nat.lt_succ_iff_lt_or_eq.1 hu with hu | rfl
        · rw [upd_other _ _ _ (by omega), upd_other _ _ _ (by omega),
            upd_other _ _ _ (by omega)]; exact jb u hu
        · rw [upd_same]
      · rw [hm', upd_other _ _ _ (fun h => hb ⟨by omega, by omega⟩),
          upd_other _ _ _ (fun h => hb ⟨by omega, by omega⟩),
          upd_other _ _ _ (fun h => ha ⟨by omega, by omega⟩)]
        exact j3 a (fun h => ha ⟨h.1, by omega⟩) (fun h => hb ⟨h.1, by omega⟩))
  have q₂ : ∀ x, (x < 4645 ∨ 4649 < x) → c₂.nreg x = c.nreg x := fun x hx => by
    rw [j1 x (by omega), q x (by omega) (by omega)]
  obtain ⟨c₃, k₃, e₃, hk₃, gm₃, gn₃, gr₃, grm₃, go₃⟩ : ∃ c₃ k₃,
      Exec P W (block [.addN 4647 4640 4640, .addN 4648 4643 4640, .storeN 4648 4647]) c₂ c₃ k₃ ∧
      k₃ = 3 ∧ c₃.nmem = upd c₂.nmem (OFFb + m) (2 * m) ∧
      (∀ x, x ≠ 4647 → x ≠ 4648 → c₃.nreg x = c₂.nreg x) ∧
      c₃.rreg = c₂.rreg ∧ c₃.rmem = c₂.rmem ∧ c₃.output = c₂.output := by
    have a0 : c₂.nreg 4640 = m := by rw [q₂ _ (by omega), r0]
    have a3 : c₂.nreg 4643 = OFFb := by rw [q₂ _ (by omega), r3]
    exec_block
    all_goals try (config_simp; simp only [a0, a3]; omega)
    refine ⟨rfl, ?_, fun x a b => ?_, rfl, rfl, rfl⟩
    · config_simp; simp only [a0, a3]; congr 1; omega
    · config_simp; simp only [upd_apply]; split_ifs <;> omega
  refine ⟨c₃, k₁ + (k₂ + k₃), .seq e₁ (.seq e₂ e₃), by omega, fun u hu => ?_, fun u hu => ?_,
    fun u hu => ?_, fun a ha => ?_, fun x hx => ?_, by rw [gr₃, j4, gr₁],
    by rw [grm₃, j5, grm₁], by rw [go₃, j6, go₁]⟩
  · rw [gm₃]
    rcases Nat.lt_or_ge u m with hu' | hu'
    · rw [upd_other _ _ _ (by omega)]; exact jo u hu'
    · rw [show u = m by omega, upd_same]
  · rw [gm₃, upd_other _ _ _ (by omega)]; exact ja u hu
  · rw [gm₃, upd_other _ _ _ (by omega)]; exact jb u hu
  · rw [gm₃, upd_other _ _ _ (fun h => ha ⟨by omega, by omega⟩)]
    exact j3 a (fun h => ha ⟨h.1, by omega⟩) (fun h => ha ⟨by omega, h.2.trans_le (by omega)⟩)
  · rw [gn₃ x (by omega) (by omega), q₂ x (by omega)]

end C2

section Graph

variable {m₀ : ℕ → ℕ} {m OFFb ADJb : ℕ} {p pi : ℕ → ℕ}

/-- The adjacency of the CSR form built by `c2Prog` is `pAdj`. -/
lemma bfAdj_c2 (hoff : ∀ u ≤ m, m₀ (OFFb + u) = 2 * u)
    (hA : ∀ u < m, m₀ (ADJb + 2 * u) = p u) (hB : ∀ u < m, m₀ (ADJb + 2 * u + 1) = pi u)
    (u v : ℕ) : bfAdj m₀ m OFFb ADJb u v ↔ pAdj p pi m u v := by
  have hs : ∀ u < m, m₀ (OFFb + u + 1) = 2 * (u + 1) := fun u hu => hoff (u + 1) (by omega)
  constructor
  · rintro ⟨hu, i, h1, h2, rfl⟩
    rw [hoff u (by omega)] at h1
    rw [hs u hu] at h2
    refine ⟨hu, ?_⟩
    rcases (show i = 2 * u ∨ i = 2 * u + 1 by omega) with rfl | rfl
    · exact Or.inl (hA u hu)
    · exact Or.inr (hB u hu)
  · rintro ⟨hu, rfl | rfl⟩
    · exact ⟨hu, 2 * u, by rw [hoff u (by omega)], by rw [hs u hu]; omega,
        hA u hu⟩
    · exact ⟨hu, 2 * u + 1, by rw [hoff u (by omega)]; omega,
        by rw [hs u hu]; omega, hB u hu⟩

lemma bfIn_c2 (hP : PermArr p pi m) (hoff : ∀ u ≤ m, m₀ (OFFb + u) = 2 * u)
    (hA : ∀ u < m, m₀ (ADJb + 2 * u) = p u) (hB : ∀ u < m, m₀ (ADJb + 2 * u + 1) = pi u) :
    BfIn m₀ m OFFb ADJb (2 * m) := by
  have e := bfAdj_c2 hoff hA hB
  have hs : ∀ u < m, m₀ (OFFb + u + 1) = 2 * (u + 1) := fun u hu => hoff (u + 1) (by omega)
  refine ⟨fun u hu => ?_, hoff m le_rfl, fun u v h => ?_, fun u v h => ?_⟩
  · rw [hoff u (by omega), hs u hu]; omega
  · obtain ⟨hu, rfl | rfl⟩ := (e u v).1 h
    · exact hP.plt u hu
    · exact hP.pilt u hu
  · exact (e v u).2 (pAdj_symm hP ((e u v).1 h))

end Graph

/-- The set-up of the orbit labelling: the registers of `c2Prog`, `bfProg`, `rkProg` from
`4650 = m`, `4651 = Pb`, `4652 = PIb`, `4653 = Sb`, `4654 = OUTb` (scratch `OFF | ADJ | LAB | Q
| T` at `Sb`, `Sb + m + 1`, `Sb + 3m + 1`, `Sb + 4m + 1`, `Sb + 5m + 2`). -/
def orbSet : Stmt :=
  block [.constN 4655 1, .copyN 4640 4650, .copyN 4641 4651, .copyN 4642 4652,
    .copyN 4643 4653, .addN 4656 4650 4655, .addN 4644 4653 4656, .copyN 4400 4650,
    .copyN 4401 4653, .copyN 4402 4644, .addN 4403 4644 4650, .addN 4403 4403 4650,
    .addN 4404 4403 4650, .copyN 4610 4650, .copyN 4611 4403, .addN 4612 4404 4656,
    .copyN 4613 4654]

/-- **The contiguous orbit numbering of an index permutation on the machine.** -/
def orbProg : Stmt := .seq orbSet (.seq c2Prog (.seq bfProg rkProg))

section Orb

variable {P : Input} {W : ℕ}

theorem orbSet_exec (c : Config) (hc : WordsBounded W c) {m Pb PIb Sb OUTb : ℕ}
    (r0 : c.nreg 4650 = m) (r1 : c.nreg 4651 = Pb) (r2 : c.nreg 4652 = PIb)
    (r3 : c.nreg 4653 = Sb) (r4 : c.nreg 4654 = OUTb) (w : Sb + 5 * m + 2 ≤ W) :
    ∃ c' k, Exec P W orbSet c c' k ∧ k = 17 ∧
      c'.nreg 4640 = m ∧ c'.nreg 4641 = Pb ∧ c'.nreg 4642 = PIb ∧ c'.nreg 4643 = Sb ∧
      c'.nreg 4644 = Sb + m + 1 ∧ c'.nreg 4400 = m ∧ c'.nreg 4401 = Sb ∧
      c'.nreg 4402 = Sb + m + 1 ∧ c'.nreg 4403 = Sb + 3 * m + 1 ∧
      c'.nreg 4404 = Sb + 4 * m + 1 ∧ c'.nreg 4610 = m ∧ c'.nreg 4611 = Sb + 3 * m + 1 ∧
      c'.nreg 4612 = Sb + 5 * m + 2 ∧ c'.nreg 4613 = OUTb ∧ c'.nmem = c.nmem ∧
      (∀ x, x ≠ 4655 → x ≠ 4656 → x ≠ 4640 → x ≠ 4641 → x ≠ 4642 → x ≠ 4643 → x ≠ 4644 →
        x ≠ 4400 → x ≠ 4401 → x ≠ 4402 → x ≠ 4403 → x ≠ 4404 → x ≠ 4610 → x ≠ 4611 →
        x ≠ 4612 → x ≠ 4613 → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hS : Sb + 5 * m + 2 ≤ W := w
  unfold orbSet
  exec_block
  all_goals try omega
  all_goals try (config_simp; simp only [r0, r1, r2, r3, r4]; omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, ?_, rfl, rfl, rfl⟩
  all_goals try (config_simp; simp only [r0, r1, r2, r3, r4] <;> omega)
  intro x a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16
  config_simp; simp only [upd_apply]; split_ifs <;> omega

/-- **The orbits of an index permutation, numbered contiguously**: with `P`, `PI` inverse arrays
of `[0, m)` (`PermArr`), outside the scratch `[Sb, Sb + 6 m + 3)` and the output
`[OUTb, OUTb + m)`, the label part `[Sb + 3m + 1, Sb + 4m + 1)` and the table part
`[Sb + 5m + 2, Sb + 6m + 3)` zero: within `85 m + 37` steps `OUT[i] = OUT[j] ↔ ReflTransGen
(pAdj P PI m) i j`, `OUT[j] < r4616`, every number `< r4616` is some `OUT[j]`; memory outside
the scratch and `OUT`, registers outside `4400 … 4416`, `4610 … 4621`, `4640 … 4656` kept. -/
theorem orbProg_exec (c : Config) (hc : WordsBounded W c) {m Pb PIb Sb OUTb : ℕ}
    (r0 : c.nreg 4650 = m) (r1 : c.nreg 4651 = Pb) (r2 : c.nreg 4652 = PIb)
    (r3 : c.nreg 4653 = Sb) (r4 : c.nreg 4654 = OUTb)
    (hP : PermArr (fun u => c.nmem (Pb + u)) (fun u => c.nmem (PIb + u)) m)
    (dP : ∀ u < m, ¬ (Sb ≤ Pb + u ∧ Pb + u < Sb + 6 * m + 3))
    (dPI : ∀ u < m, ¬ (Sb ≤ PIb + u ∧ PIb + u < Sb + 6 * m + 3))
    (dO : Sb + 6 * m + 3 ≤ OUTb ∨ OUTb + m ≤ Sb)
    (hz : ∀ a, Sb + 3 * m + 1 ≤ a → a < Sb + 4 * m + 1 → c.nmem a = 0)
    (hz' : ∀ a, Sb + 5 * m + 2 ≤ a → a < Sb + 6 * m + 3 → c.nmem a = 0)
    (w1 : Sb + 6 * m + 3 ≤ W) (w2 : Pb + m ≤ W) (w3 : PIb + m ≤ W) (w4 : OUTb + m ≤ W) :
    ∃ c' k, Exec P W orbProg c c' k ∧ k ≤ 85 * m + 37 ∧
      (∀ i < m, ∀ j < m, (c'.nmem (OUTb + i) = c'.nmem (OUTb + j) ↔
        ReflTransGen (pAdj (fun u => c.nmem (Pb + u)) (fun u => c.nmem (PIb + u)) m) i j)) ∧
      (∀ j < m, c'.nmem (OUTb + j) < c'.nreg 4616) ∧
      (∀ r < c'.nreg 4616, ∃ j < m, c'.nmem (OUTb + j) = r) ∧ c'.nreg 4616 ≤ m ∧
      (∀ a, ¬ (Sb ≤ a ∧ a < Sb + 6 * m + 3) → ¬ (OUTb ≤ a ∧ a < OUTb + m) →
        c'.nmem a = c.nmem a) ∧
      (∀ x, (x < 4400 ∨ (4416 < x ∧ x < 4610) ∨ (4621 < x ∧ x < 4640) ∨ 4656 < x) →
        c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold orbProg
  obtain ⟨c₁, k₁, e₁, hk₁, a40, a41, a42, a43, a44, b0, b1, b2, b3, b4, k0, k1, k2, k3, gm₁,
    gn₁, gr₁, grm₁, go₁⟩ := orbSet_exec (P := P) c hc r0 r1 r2 r3 r4 (by omega)
  have hw₁ := e₁.wb_right
  -- the CSR form
  obtain ⟨c₂, k₂, e₂, hk₂, ho₂, hA₂, hB₂, gm₂, gn₂, gr₂, grm₂, go₂⟩ :=
    c2Prog_exec (P := P) c₁ hw₁ a40 a41 a42 a43 a44 (by omega)
      (fun u hu h => dP u hu ⟨h.1, by omega⟩) (fun u hu h => dPI u hu ⟨h.1, by omega⟩)
      (by omega) (by omega) (by omega)
  have hw₂ := e₂.wb_right
  rw [gm₁] at hA₂ hB₂
  have hoff : ∀ u ≤ m, c₂.nmem (Sb + u) = 2 * u := ho₂
  have hA : ∀ u < m, c₂.nmem (Sb + m + 1 + 2 * u) = c.nmem (Pb + u) := hA₂
  have hB : ∀ u < m, c₂.nmem (Sb + m + 1 + 2 * u + 1) = c.nmem (PIb + u) := hB₂
  have hIn := bfIn_c2 hP hoff hA hB
  have hadj := bfAdj_c2 hoff hA hB
  -- the labels
  obtain ⟨c₃, k₃, e₃, hk₃, hl₃, hpos₃, gm₃, gn₃, gr₃, grm₃, go₃⟩ :=
    bfProg_exec (P := P) c₂ hw₂ (N := m) (E := 2 * m) (OFFb := Sb) (ADJb := Sb + m + 1)
      (LABb := Sb + 3 * m + 1) (Qb := Sb + 4 * m + 1) ⟨by omega, by omega, by omega, by omega⟩
      hIn (by rw [gn₂ _ (by omega), b0]) (by rw [gn₂ _ (by omega), b1])
      (by rw [gn₂ _ (by omega), b2]) (by rw [gn₂ _ (by omega), b3])
      (by rw [gn₂ _ (by omega), b4])
      (fun u hu => by rw [gm₂ _ (fun h => by omega), gm₁]; exact hz _ (by omega) (by omega))
  have hw₃ := e₃.wb_right
  -- the rank
  obtain ⟨c₄, k₄, e₄, hk₄, hO₄, hC₄, -, gm₄, gn₄, gr₄, grm₄, go₄⟩ :=
    rkProg_exec (P := P) c₃ hw₃ (m := m) (nk := m + 1) (LABb := Sb + 3 * m + 1)
      (Tb := Sb + 5 * m + 2) (OUTb := OUTb)
      (by rw [gn₃ _ (by omega), gn₂ _ (by omega), k0])
      (by rw [gn₃ _ (by omega), gn₂ _ (by omega), k1])
      (by rw [gn₃ _ (by omega), gn₂ _ (by omega), k2])
      (by rw [gn₃ _ (by omega), gn₂ _ (by omega), k3])
      (fun j hj => by have := (hpos₃ j hj).2; omega)
      (fun k hk => by
        rw [gm₃ _ (fun h => by omega) (fun h => by omega), gm₂ _ (fun h => by omega), gm₁]
        exact hz' _ (by omega) (by omega))
      ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
  set lab : ℕ → ℕ := fun j => c₃.nmem (Sb + 3 * m + 1 + j) with hlab
  obtain ⟨f1, f2, f3⟩ := rk_final (lab := lab) m
  have hrt : ∀ i < m, ∀ j < m, (lab i = lab j ↔
      ReflTransGen (pAdj (fun u => c.nmem (Pb + u)) (fun u => c.nmem (PIb + u)) m) i j) := by
    intro i hi j hj
    rw [hl₃ i hi j hj]
    have hf : bfAdj c₂.nmem m Sb (Sb + m + 1) =
        pAdj (fun u => c.nmem (Pb + u)) (fun u => c.nmem (PIb + u)) m := by
      funext u v; exact propext (hadj u v)
    rw [hf]
  refine ⟨c₄, k₁ + (k₂ + (k₃ + k₄)), .seq e₁ (.seq e₂ (.seq e₃ e₄)), by omega,
    fun i hi j hj => ?_, fun j hj => ?_, fun r hr => ?_, ?_, fun a ha hb => ?_,
    fun x hx => ?_, by rw [gr₄, gr₃, gr₂, gr₁], by rw [grm₄, grm₃, grm₂, grm₁],
    by rw [go₄, go₃, go₂, go₁]⟩
  · rw [hO₄ i hi, hO₄ j hj]; exact (f1 i hi j hj).trans (hrt i hi j hj)
  · rw [hO₄ j hj, hC₄]; exact f2 j hj
  · rw [hC₄] at hr
    obtain ⟨j, hj, e⟩ := f3 r hr
    exact ⟨j, hj, by rw [hO₄ j hj]; exact e⟩
  · rw [hC₄]; exact rkC_le m
  · rw [gm₄ _ (fun h => ha ⟨by omega, by omega⟩) hb,
      gm₃ _ (fun h => ha ⟨by omega, by omega⟩) (fun h => ha ⟨by omega, by omega⟩),
      gm₂ _ (fun h => ha ⟨h.1, by omega⟩), gm₁]
  · rw [gn₄ x (by omega), gn₃ x (by omega), gn₂ x (by omega)]
    exact gn₁ x (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega)

end Orb

end BKMNW

end PlanarFlow
