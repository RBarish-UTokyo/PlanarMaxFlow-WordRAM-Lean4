module

public import PlanarFlow.BKMNW.OrbProg
public import PlanarFlow.BKMNW.GatherProg

/-!
# The plain encoding of a piece map built on the machine

From the index arrays of a piece (darts numbered `0 … m-1`): the reversal `REV` at `B₀`, the
rotation `SIG` at `SIGb`, the extra weights `EX` at `EXb`, the program `encProg` writes the plain
encoding read by Miller's program `msep` (`msep_spec`): `α = REV` at `B₀` (in place), `φ = SIG ∘
REV` at `B₀ + m` (`gaProg`), `φ⁻¹` at `B₀ + 2m` (`invProg`), the vertex numbers (orbits of `SIG`,
`orbProg` with the inverse `SIG⁻¹` from `invProg`) at `B₀ + 3m`, the face numbers (orbits of `φ`)
at `B₀ + 4m`, the vertex weights `Σ EX` (`saProg`) at `B₀ + 5m` and the face weights (number of
darts, `saProg` on a constant cell) after them; then `r390 … r393 = m, nV, nF, B₀`.

* pure: `iter_lt`, `iter_left`, `permArr_period`, **`rtg_pAdj_iff`** (`ReflTransGen (pAdj p pi m)
  i j ↔ ∃ k, p^[k] i = j`), `surj_of_inj`, `permArr_of_inv`.
* stages `enSet`, `enGa`, `enI1`, `enI2`, `enO1`, `enO2`, `enA1`, `enA2`, `enFin` with exec
  lemmas; **`encProg`**; **`encProg_exec`** (within `encT m = 217 m + 160` steps).
Registers: inputs `4660 = m`, `4661 = B₀`, `4662 = SIGb`, `4663 = EXb`, `4664 = Sb` (scratch
`13 m + 7` words, zero); addresses `4667 … 4682`.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace PlanarFlow

namespace BKMNW

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs Relation

/-! ### Orbits of an index permutation as iterates -/

section Pure

variable {p pi : ℕ → ℕ} {m : ℕ}

lemma iter_lt (h : ∀ u < m, p u < m) (k : ℕ) {x : ℕ} (hx : x < m) : p^[k] x < m := by
  induction k with
  | zero => exact hx
  | succ k ih => rw [Function.iterate_succ_apply']; exact h _ ih

lemma iter_left (h : PermArr p pi m) (k : ℕ) {x : ℕ} (hx : x < m) : pi^[k] (p^[k] x) = x := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply' p k x, Function.iterate_succ_apply pi k,
      h.left _ (iter_lt h.plt k hx), ih]

/-- Every index returns to itself. -/
lemma permArr_period (h : PermArr p pi m) {i : ℕ} (hi : i < m) : ∃ n, 0 < n ∧ p^[n] i = i := by
  have hc : #(range m) < #(range (m + 1)) := by simp
  obtain ⟨a, ha, b, hb, hab, e⟩ := exists_ne_map_eq_of_card_lt_of_maps_to hc
    (f := fun k => p^[k] i) (fun k _ => by simp only [coe_range, Set.mem_Iio]; exact iter_lt h.plt k hi)
  have key : ∀ a b, a < b → p^[a] i = p^[b] i → ∃ n, 0 < n ∧ p^[n] i = i := by
    intro a b hlt e
    refine ⟨b - a, by omega, ?_⟩
    have h1 : p^[b] i = p^[a] (p^[b - a] i) := by
      rw [← Function.iterate_add_apply, show a + (b - a) = b by omega]
    rw [h1] at e
    have h2 := congrArg (pi^[a]) e
    rwa [iter_left h a hi, iter_left h a (iter_lt h.plt _ hi), eq_comm] at h2
  rcases Nat.lt_or_gt_of_ne hab with hlt | hlt
  · exact key a b hlt e
  · exact key b a hlt e.symm

/-- **The orbit graph of an index permutation**: `j` is reachable from `i` iff it is an iterate. -/
theorem rtg_pAdj_iff (h : PermArr p pi m) {i j : ℕ} (hi : i < m) :
    ReflTransGen (pAdj p pi m) i j ↔ ∃ k, p^[k] i = j := by
  constructor
  · intro hr
    induction hr with
    | refl => exact ⟨0, rfl⟩
    | tail _ hst ih =>
      obtain ⟨k, hk⟩ := ih
      obtain ⟨hb, rfl | rfl⟩ := hst
      · exact ⟨k + 1, by rw [Function.iterate_succ_apply', hk]⟩
      · obtain ⟨n, hn, hp⟩ := permArr_period h hi
        refine ⟨k + n - 1, ?_⟩
        have e : p (p^[k + n - 1] i) = p^[k] i := by
          rw [← Function.iterate_succ_apply' p, show (k + n - 1).succ = k + n by omega,
            Function.iterate_add_apply, hp]
        rw [← hk, ← e, h.left _ (iter_lt h.plt _ hi)]
  · rintro ⟨k, rfl⟩
    induction k with
    | zero => exact .refl
    | succ k ih =>
      exact ih.tail ⟨iter_lt h.plt k hi, Or.inl (Function.iterate_succ_apply' _ _ _)⟩

/-- An injective self-map of `[0, m)` is onto. -/
lemma surj_of_inj {f : ℕ → ℕ} (hlt : ∀ u < m, f u < m)
    (hinj : ∀ i < m, ∀ j < m, f i = f j → i = j) : ∀ u < m, ∃ j < m, f j = u := by
  have hsub : (range m).image f ⊆ range m := by
    intro x hx
    obtain ⟨j, hj, rfl⟩ := mem_image.1 hx
    exact mem_range.2 (hlt j (mem_range.1 hj))
  have hcard : #(range m) ≤ #((range m).image f) := by
    rw [card_image_of_injOn (fun i hi j hj e => hinj i (mem_range.1 hi) j (mem_range.1 hj) e)]
  have heq := eq_of_subset_of_card_le hsub hcard
  intro u hu
  have : u ∈ (range m).image f := by rw [heq]; exact mem_range.2 hu
  obtain ⟨j, hj, e⟩ := mem_image.1 this
  exact ⟨j, mem_range.1 hj, e⟩

lemma permArr_of_inv (hlt : ∀ u < m, p u < m) (hinj : ∀ i < m, ∀ j < m, p i = p j → i = j)
    (hinv : ∀ j < m, pi (p j) = j) : PermArr p pi m := by
  have hs := surj_of_inj hlt hinj
  refine ⟨hlt, fun u hu => ?_, hinv, fun u hu => ?_⟩
  · obtain ⟨j, hj, rfl⟩ := hs u hu; rw [hinv j hj]; exact hj
  · obtain ⟨j, hj, rfl⟩ := hs u hu; rw [hinv j hj]

lemma iter_congr {f g : ℕ → ℕ} (hf : ∀ u < m, f u < m) (h : ∀ u < m, f u = g u) (k : ℕ)
    {x : ℕ} (hx : x < m) : f^[k] x = g^[k] x := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih,
      h _ (iter_lt hf k hx)]

lemma saF_congr {key key' val val' : ℕ → ℕ} (hk : ∀ j < m, key j = key' j)
    (hv : ∀ j < m, val j = val' j) (k : ℕ) : saF key val m k = saF key' val' m k := by
  unfold saF
  have : (range m).filter (fun j => key j = k) = (range m).filter (fun j => key' j = k) := by
    ext j; simp only [mem_filter, mem_range]
    exact ⟨fun ⟨a, b⟩ => ⟨a, by rw [← hk j a]; exact b⟩, fun ⟨a, b⟩ => ⟨a, by rw [hk j a]; exact b⟩⟩
  rw [this]
  exact sum_congr rfl (fun j hj => hv j (mem_range.1 (mem_filter.1 hj).1))

end Pure

/-! ### The stages -/

/-- The addresses: `4667 = 1`, `4668 … 4672 = B₀ + m … B₀ + 5m`, `4673 = Sb + m`,
`4674 = 2m`, `4675 = 6m + 3`, `4676 = Sb + 7m + 3`, `4677 = Sb + 13m + 6` (a cell set to `1`). -/
def enSet : Stmt :=
  block [.constN 4667 1, .addN 4668 4661 4660, .addN 4669 4668 4660, .addN 4670 4669 4660,
    .addN 4671 4670 4660, .addN 4672 4671 4660, .addN 4673 4664 4660, .addN 4674 4660 4660,
    .addN 4675 4674 4674, .addN 4675 4675 4674, .addN 4675 4675 4667, .addN 4675 4675 4667,
    .addN 4675 4675 4667, .addN 4676 4673 4675, .addN 4677 4676 4675, .storeN 4677 4667]

/-- `φ := SIG ∘ REV` at `B₀ + m`. -/
def enGa : Stmt :=
  .seq (block [.copyN 4470 4660, .copyN 4471 4661, .copyN 4472 4662, .copyN 4473 4668]) gaProg

/-- `φ⁻¹` at `B₀ + 2m`. -/
def enI1 : Stmt :=
  .seq (block [.copyN 4600 4660, .copyN 4601 4668, .copyN 4602 4669]) invProg

/-- `SIG⁻¹` at `Sb`. -/
def enI2 : Stmt :=
  .seq (block [.copyN 4600 4660, .copyN 4601 4662, .copyN 4602 4664]) invProg

/-- The vertex numbers at `B₀ + 3m` (scratch at `Sb + m`); `nV` into `4678`. -/
def enO1 : Stmt :=
  .seq (block [.copyN 4650 4660, .copyN 4651 4662, .copyN 4652 4664, .copyN 4653 4673,
    .copyN 4654 4670]) (.seq orbProg (block [.copyN 4678 4616]))

/-- The face numbers at `B₀ + 4m` (scratch at `Sb + 7m + 3`); `nF` into `4679`. -/
def enO2 : Stmt :=
  .seq (block [.copyN 4650 4660, .copyN 4651 4668, .copyN 4652 4669, .copyN 4653 4676,
    .copyN 4654 4671]) (.seq orbProg (block [.copyN 4679 4616]))

/-- The vertex weights `Σ EX` at `B₀ + 5m`. -/
def enA1 : Stmt :=
  .seq (block [.copyN 4630 4660, .copyN 4631 4670, .copyN 4632 4663, .copyN 4633 4667,
    .copyN 4634 4672]) saProg

/-- The face weights (numbers of darts) at `B₀ + 5m + nV`. -/
def enA2 : Stmt :=
  .seq (block [.constN 4681 0, .addN 4682 4672 4678, .copyN 4630 4660, .copyN 4631 4671,
    .copyN 4632 4677, .copyN 4633 4681, .copyN 4634 4682]) saProg

/-- The registers of `msep`. -/
def enFin : Stmt := block [.copyN 390 4660, .copyN 391 4678, .copyN 392 4679, .copyN 393 4661]

/-- **The plain encoding of a piece map on the machine.** -/
def encProg : Stmt :=
  .seq enSet (.seq enGa (.seq enI1 (.seq enI2 (.seq enO1 (.seq enO2 (.seq enA1
    (.seq enA2 enFin)))))))


section Stages

variable {P : Input} {W : ℕ}

theorem enSet_exec (c : Config) (hc : WordsBounded W c) {m B₀ Sb : ℕ}
    (r60 : c.nreg 4660 = m) (r61 : c.nreg 4661 = B₀) (r64 : c.nreg 4664 = Sb)
    (w0 : B₀ + 7 * m ≤ W) (w : Sb + 13 * m + 7 ≤ W) :
    ∃ c' k, Exec P W enSet c c' k ∧ k = 16 ∧ c'.nreg 4667 = 1 ∧ c'.nreg 4668 = B₀ + m ∧
      c'.nreg 4669 = B₀ + 2 * m ∧ c'.nreg 4670 = B₀ + 3 * m ∧ c'.nreg 4671 = B₀ + 4 * m ∧
      c'.nreg 4672 = B₀ + 5 * m ∧ c'.nreg 4673 = Sb + m ∧ c'.nreg 4676 = Sb + 7 * m + 3 ∧
      c'.nreg 4677 = Sb + 13 * m + 6 ∧ c'.nmem = upd c.nmem (Sb + 13 * m + 6) 1 ∧
      (∀ x, (x < 4667 ∨ 4677 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold enSet
  exec_block
  all_goals try omega
  all_goals try (first | (config_simp; done) | (config_simp; simp only [r60, r61, r64] <;> omega))
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun x hx => ?_, rfl, rfl, rfl⟩
  all_goals try (first | (config_simp; done) | (config_simp; simp only [r60, r61, r64] <;> omega))
  · config_simp; simp only [r60, r61, r64]; congr 1; omega
  · obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11⟩ : x ≠ 4667 ∧ x ≠ 4668 ∧ x ≠ 4669 ∧
        x ≠ 4670 ∧ x ≠ 4671 ∧ x ≠ 4672 ∧ x ≠ 4673 ∧ x ≠ 4674 ∧ x ≠ 4675 ∧ x ≠ 4676 ∧
        x ≠ 4677 := by omega
    simp only [Config.nreg_mk, upd_other _ _ _ a1, upd_other _ _ _ a2, upd_other _ _ _ a3,
      upd_other _ _ _ a4, upd_other _ _ _ a5, upd_other _ _ _ a6, upd_other _ _ _ a7,
      upd_other _ _ _ a8, upd_other _ _ _ a9, upd_other _ _ _ a10, upd_other _ _ _ a11]

theorem enGa_exec (c : Config) (hc : WordsBounded W c) {m B₀ SIGb : ℕ}
    (r60 : c.nreg 4660 = m) (r61 : c.nreg 4661 = B₀) (r62 : c.nreg 4662 = SIGb)
    (r68 : c.nreg 4668 = B₀ + m) (hREV : ∀ j < m, c.nmem (B₀ + j) < m)
    (lay : B₀ + 7 * m ≤ SIGb) (w : SIGb + m ≤ W) (w1 : m + 1 ≤ W) :
    ∃ c' k, Exec P W enGa c c' k ∧ k ≤ 9 * m + 8 ∧
      (∀ j < m, c'.nmem (B₀ + m + j) = c.nmem (SIGb + c.nmem (B₀ + j))) ∧
      (∀ a, ¬ (B₀ + m ≤ a ∧ a < B₀ + 2 * m) → c'.nmem a = c.nmem a) ∧
      (∀ x, 4659 < x → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold enGa
  obtain ⟨c₁, k₁, e₁, hk₁, g0, g1, g2, g3, gn₁, gm₁, gr₁, grm₁, go₁⟩ : ∃ c₁ k₁,
      Exec P W (block [.copyN 4470 4660, .copyN 4471 4661, .copyN 4472 4662, .copyN 4473 4668])
        c c₁ k₁ ∧ k₁ = 4 ∧ c₁.nreg 4470 = m ∧ c₁.nreg 4471 = B₀ ∧ c₁.nreg 4472 = SIGb ∧
      c₁.nreg 4473 = B₀ + m ∧
      (∀ x, x ≠ 4470 → x ≠ 4471 → x ≠ 4472 → x ≠ 4473 → c₁.nreg x = c.nreg x) ∧
      c₁.nmem = c.nmem ∧ c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    exec_block
    all_goals try omega
    all_goals try (first | (config_simp; done) | (config_simp; simp only [r60, r61, r62, r68] <;> omega))
    refine ⟨rfl, ?_, ?_, ?_, ?_, fun x a b d e => ?_, rfl, rfl, rfl, rfl⟩
    all_goals try (first | (config_simp; done) | (config_simp; simp only [r60, r61, r62, r68] <;> omega))
    config_simp; simp only [upd_apply]; split_ifs <;> omega
  have hw₁ := e₁.wb_right
  obtain ⟨c₂, k₂, e₂, hk₂, h₂, gm₂, gn₂, gr₂, grm₂, go₂⟩ := gaProg_exec (P := P) c₁ hw₁
    (m := m) g0 g1 g2 g3 (by omega) (by omega) w1
    (fun j hj => by rw [gm₁]; have := hREV j hj; omega)
    (fun j hj h => by omega) (fun j hj h => by rw [gm₁] at h; omega)
  refine ⟨c₂, k₁ + k₂, .seq e₁ e₂, by omega, fun j hj => ?_, fun a ha => ?_, fun x hx => ?_,
    by rw [gr₂, gr₁], by rw [grm₂, grm₁], by rw [go₂, go₁]⟩
  · rw [h₂ j hj, gm₁]
  · rw [gm₂ a (fun h => ha ⟨by omega, by omega⟩), gm₁]
  · rw [gn₂ x (by omega), gn₁ x (by omega) (by omega) (by omega) (by omega)]

theorem enInv_core (c : Config) (hc : WordsBounded W c) {m Pb OUTb : ℕ}
    (r0 : c.nreg 4600 = m) (r1 : c.nreg 4601 = Pb) (r2 : c.nreg 4602 = OUTb)
    (hlt : ∀ j < m, c.nmem (Pb + j) < m)
    (hinj : ∀ i < m, ∀ j < m, c.nmem (Pb + i) = c.nmem (Pb + j) → i = j)
    (lay : Pb + m ≤ OUTb ∨ OUTb + m ≤ Pb) (w : Pb + m ≤ W) (w' : OUTb + m ≤ W)
    (w1 : m + 1 ≤ W) :
    ∃ c' k, Exec P W invProg c c' k ∧ k ≤ 7 * m + 4 ∧
      (∀ j < m, c'.nmem (OUTb + c.nmem (Pb + j)) = j) ∧
      (∀ a, ¬ (OUTb ≤ a ∧ a < OUTb + m) → c'.nmem a = c.nmem a) ∧
      (∀ x, (x < 4603 ∨ 4605 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c', k, e, hk, h1, h2, h3, h4, h5, h6⟩ := invProg_exec (P := P) c hc r0 r1 r2 w w1
    (fun j hj => by have := hlt j hj; omega) hinj
    (fun i hi j hj h => by have := hlt j hj; omega)
  exact ⟨c', k, e, hk, h1, fun a ha => h2 a (fun j hj h => ha ⟨by omega,
    by have := hlt j hj; omega⟩), h3, h4, h5, h6⟩

theorem enI1_exec (c : Config) (hc : WordsBounded W c) {m B₀ : ℕ}
    (r60 : c.nreg 4660 = m) (r68 : c.nreg 4668 = B₀ + m) (r69 : c.nreg 4669 = B₀ + 2 * m)
    (hlt : ∀ j < m, c.nmem (B₀ + m + j) < m)
    (hinj : ∀ i < m, ∀ j < m, c.nmem (B₀ + m + i) = c.nmem (B₀ + m + j) → i = j)
    (w : B₀ + 3 * m ≤ W) (w1 : m + 1 ≤ W) :
    ∃ c' k, Exec P W enI1 c c' k ∧ k ≤ 7 * m + 7 ∧
      (∀ j < m, c'.nmem (B₀ + 2 * m + c.nmem (B₀ + m + j)) = j) ∧
      (∀ a, ¬ (B₀ + 2 * m ≤ a ∧ a < B₀ + 3 * m) → c'.nmem a = c.nmem a) ∧
      (∀ x, 4659 < x → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold enI1
  obtain ⟨c₁, k₁, e₁, hk₁, g0, g1, g2, gn₁, gm₁, gr₁, grm₁, go₁⟩ : ∃ c₁ k₁,
      Exec P W (block [.copyN 4600 4660, .copyN 4601 4668, .copyN 4602 4669]) c c₁ k₁ ∧
      k₁ = 3 ∧ c₁.nreg 4600 = m ∧ c₁.nreg 4601 = B₀ + m ∧ c₁.nreg 4602 = B₀ + 2 * m ∧
      (∀ x, x ≠ 4600 → x ≠ 4601 → x ≠ 4602 → c₁.nreg x = c.nreg x) ∧
      c₁.nmem = c.nmem ∧ c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    exec_block
    all_goals try omega
    all_goals try (first | (config_simp; done) | (config_simp; simp only [r60, r68, r69] <;> omega))
    refine ⟨rfl, ?_, ?_, ?_, fun x a b d => ?_, rfl, rfl, rfl, rfl⟩
    all_goals try (first | (config_simp; done) | (config_simp; simp only [r60, r68, r69] <;> omega))
    config_simp; simp only [upd_apply]; split_ifs <;> omega
  have hw₁ := e₁.wb_right
  rw [← gm₁] at hlt hinj
  obtain ⟨c₂, k₂, e₂, hk₂, h₂, gm₂, gn₂, gr₂, grm₂, go₂⟩ := enInv_core (P := P) c₁ hw₁
    g0 g1 g2 hlt hinj (by omega) (by omega) (by omega) w1
  refine ⟨c₂, k₁ + k₂, .seq e₁ e₂, by omega, fun j hj => ?_, fun a ha => ?_, fun x hx => ?_,
    by rw [gr₂, gr₁], by rw [grm₂, grm₁], by rw [go₂, go₁]⟩
  · rw [← gm₁]; exact h₂ j hj
  · rw [gm₂ a (fun h => ha ⟨h.1, by omega⟩), gm₁]
  · rw [gn₂ x (by omega), gn₁ x (by omega) (by omega) (by omega)]

theorem enI2_exec (c : Config) (hc : WordsBounded W c) {m SIGb Sb : ℕ}
    (r60 : c.nreg 4660 = m) (r62 : c.nreg 4662 = SIGb) (r64 : c.nreg 4664 = Sb)
    (hlt : ∀ j < m, c.nmem (SIGb + j) < m)
    (hinj : ∀ i < m, ∀ j < m, c.nmem (SIGb + i) = c.nmem (SIGb + j) → i = j)
    (lay : SIGb + m ≤ Sb) (w : Sb + m ≤ W) (w1 : m + 1 ≤ W) :
    ∃ c' k, Exec P W enI2 c c' k ∧ k ≤ 7 * m + 7 ∧
      (∀ j < m, c'.nmem (Sb + c.nmem (SIGb + j)) = j) ∧
      (∀ a, ¬ (Sb ≤ a ∧ a < Sb + m) → c'.nmem a = c.nmem a) ∧
      (∀ x, 4659 < x → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold enI2
  obtain ⟨c₁, k₁, e₁, hk₁, g0, g1, g2, gn₁, gm₁, gr₁, grm₁, go₁⟩ : ∃ c₁ k₁,
      Exec P W (block [.copyN 4600 4660, .copyN 4601 4662, .copyN 4602 4664]) c c₁ k₁ ∧
      k₁ = 3 ∧ c₁.nreg 4600 = m ∧ c₁.nreg 4601 = SIGb ∧ c₁.nreg 4602 = Sb ∧
      (∀ x, x ≠ 4600 → x ≠ 4601 → x ≠ 4602 → c₁.nreg x = c.nreg x) ∧
      c₁.nmem = c.nmem ∧ c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    exec_block
    all_goals try omega
    all_goals try (first | (config_simp; done) | (config_simp; simp only [r60, r62, r64] <;> omega))
    refine ⟨rfl, ?_, ?_, ?_, fun x a b d => ?_, rfl, rfl, rfl, rfl⟩
    all_goals try (first | (config_simp; done) | (config_simp; simp only [r60, r62, r64] <;> omega))
    config_simp; simp only [upd_apply]; split_ifs <;> omega
  have hw₁ := e₁.wb_right
  rw [← gm₁] at hlt hinj
  obtain ⟨c₂, k₂, e₂, hk₂, h₂, gm₂, gn₂, gr₂, grm₂, go₂⟩ := enInv_core (P := P) c₁ hw₁
    g0 g1 g2 hlt hinj (by omega) (by omega) (by omega) w1
  refine ⟨c₂, k₁ + k₂, .seq e₁ e₂, by omega, fun j hj => ?_, fun a ha => ?_, fun x hx => ?_,
    by rw [gr₂, gr₁], by rw [grm₂, grm₁], by rw [go₂, go₁]⟩
  · rw [← gm₁]; exact h₂ j hj
  · rw [gm₂ a ha, gm₁]
  · rw [gn₂ x (by omega), gn₁ x (by omega) (by omega) (by omega)]

/-- The orbit stage after its register copies: `orbProg` and the copy of the count. -/
theorem enOrb_core (c : Config) (hc : WordsBounded W c) {m Pb PIb Sb OUTb : ℕ} (rN : ℕ)
    (r0 : c.nreg 4650 = m) (r1 : c.nreg 4651 = Pb) (r2 : c.nreg 4652 = PIb)
    (r3 : c.nreg 4653 = Sb) (r4 : c.nreg 4654 = OUTb)
    (hP : PermArr (fun u => c.nmem (Pb + u)) (fun u => c.nmem (PIb + u)) m)
    (dP : ∀ u < m, ¬ (Sb ≤ Pb + u ∧ Pb + u < Sb + 6 * m + 3))
    (dPI : ∀ u < m, ¬ (Sb ≤ PIb + u ∧ PIb + u < Sb + 6 * m + 3))
    (dO : Sb + 6 * m + 3 ≤ OUTb ∨ OUTb + m ≤ Sb)
    (hz : ∀ a, Sb ≤ a → a < Sb + 6 * m + 3 → c.nmem a = 0)
    (w1 : Sb + 6 * m + 3 ≤ W) (w2 : Pb + m ≤ W) (w3 : PIb + m ≤ W) (w4 : OUTb + m ≤ W) :
    ∃ c' k, Exec P W (.seq orbProg (block [.copyN rN 4616])) c c' k ∧ k ≤ 85 * m + 38 ∧
      (∀ i < m, ∀ j < m, (c'.nmem (OUTb + i) = c'.nmem (OUTb + j) ↔
        ∃ k, (fun u => c.nmem (Pb + u))^[k] i = j)) ∧
      (∀ j < m, c'.nmem (OUTb + j) < c'.nreg rN) ∧
      (∀ r < c'.nreg rN, ∃ j < m, c'.nmem (OUTb + j) = r) ∧ c'.nreg rN ≤ m ∧
      (∀ a, ¬ (Sb ≤ a ∧ a < Sb + 6 * m + 3) → ¬ (OUTb ≤ a ∧ a < OUTb + m) →
        c'.nmem a = c.nmem a) ∧
      (∀ x, 4659 < x → x ≠ rN → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c₁, k₁, e₁, hk₁, h1, h2, h3, h4, gm₁, gn₁, gr₁, grm₁, go₁⟩ :=
    orbProg_exec (P := P) c hc r0 r1 r2 r3 r4 hP dP dPI dO
      (fun a h h' => hz a (by omega) (by omega)) (fun a h h' => hz a (by omega) (by omega))
      w1 w2 w3 w4
  have hw₁ := e₁.wb_right
  obtain ⟨c₂, k₂, e₂, hk₂, g0, gn₂, gm₂, gr₂, grm₂, go₂⟩ : ∃ c₂ k₂,
      Exec P W (block [.copyN rN 4616]) c₁ c₂ k₂ ∧ k₂ = 1 ∧ c₂.nreg rN = c₁.nreg 4616 ∧
      (∀ x, x ≠ rN → c₂.nreg x = c₁.nreg x) ∧ c₂.nmem = c₁.nmem ∧
      c₂.rreg = c₁.rreg ∧ c₁.rmem = c₂.rmem ∧ c₂.output = c₁.output := by
    exec_block
    all_goals try exact hw₁.1 _
    refine ⟨rfl, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
    · config_simp
    · config_simp; simp only [upd_apply]; split_ifs <;> simp_all
  refine ⟨c₂, k₁ + k₂, .seq e₁ e₂, by omega, fun i hi j hj => ?_, fun j hj => ?_,
    fun r hr => ?_, ?_, fun a ha hb => ?_, fun x hx hx' => ?_, by rw [gr₂, gr₁],
    by rw [← grm₂, grm₁], by rw [go₂, go₁]⟩
  · rw [gm₂, h1 i hi j hj]; exact rtg_pAdj_iff hP hi
  · rw [gm₂, g0]; exact h2 j hj
  · rw [g0] at hr; obtain ⟨j, hj, e⟩ := h3 r hr; exact ⟨j, hj, by rw [gm₂]; exact e⟩
  · rw [g0]; exact h4
  · rw [gm₂, gm₁ a ha hb]
  · rw [gn₂ x hx', gn₁ x (by omega)]


theorem enO1_exec (c : Config) (hc : WordsBounded W c) {m B₀ SIGb Sb : ℕ}
    (r60 : c.nreg 4660 = m) (r62 : c.nreg 4662 = SIGb) (r64 : c.nreg 4664 = Sb)
    (r73 : c.nreg 4673 = Sb + m) (r70 : c.nreg 4670 = B₀ + 3 * m)
    (hP : PermArr (fun u => c.nmem (SIGb + u)) (fun u => c.nmem (Sb + u)) m)
    (lay : B₀ + 4 * m ≤ SIGb) (lay2 : SIGb + m ≤ Sb) (w : Sb + 7 * m + 3 ≤ W)
    (hz : ∀ a, Sb + m ≤ a → a < Sb + 7 * m + 3 → c.nmem a = 0) :
    ∃ c' k, Exec P W enO1 c c' k ∧ k ≤ 85 * m + 43 ∧
      (∀ i < m, ∀ j < m, (c'.nmem (B₀ + 3 * m + i) = c'.nmem (B₀ + 3 * m + j) ↔
        ∃ k, (fun u => c.nmem (SIGb + u))^[k] i = j)) ∧
      (∀ j < m, c'.nmem (B₀ + 3 * m + j) < c'.nreg 4678) ∧
      (∀ r < c'.nreg 4678, ∃ j < m, c'.nmem (B₀ + 3 * m + j) = r) ∧ c'.nreg 4678 ≤ m ∧
      (∀ a, ¬ (Sb + m ≤ a ∧ a < Sb + 7 * m + 3) → ¬ (B₀ + 3 * m ≤ a ∧ a < B₀ + 4 * m) →
        c'.nmem a = c.nmem a) ∧
      (∀ x, 4659 < x → x ≠ 4678 → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold enO1
  obtain ⟨c₁, k₁, e₁, hk₁, g0, g1, g2, g3, g4, gn₁, gm₁, gr₁, grm₁, go₁⟩ : ∃ c₁ k₁,
      Exec P W (block [.copyN 4650 4660, .copyN 4651 4662, .copyN 4652 4664, .copyN 4653 4673,
        .copyN 4654 4670]) c c₁ k₁ ∧ k₁ = 5 ∧ c₁.nreg 4650 = m ∧ c₁.nreg 4651 = SIGb ∧
      c₁.nreg 4652 = Sb ∧ c₁.nreg 4653 = Sb + m ∧ c₁.nreg 4654 = B₀ + 3 * m ∧
      (∀ x, 4659 < x → c₁.nreg x = c.nreg x) ∧
      c₁.nmem = c.nmem ∧ c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    exec_block
    all_goals try omega
    all_goals try (first | (config_simp; done) | (config_simp; simp only [r60, r62, r64, r73, r70] <;> omega))
    refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
    all_goals try (first | (config_simp; done) | (config_simp; simp only [r60, r62, r64, r73, r70] <;> omega))
    obtain ⟨a1, a2, a3, a4, a5⟩ : x ≠ 4650 ∧ x ≠ 4651 ∧ x ≠ 4652 ∧ x ≠ 4653 ∧ x ≠ 4654 := by
      omega
    simp only [Config.nreg_mk, upd_other _ _ _ a1, upd_other _ _ _ a2, upd_other _ _ _ a3,
      upd_other _ _ _ a4, upd_other _ _ _ a5]
  have hw₁ := e₁.wb_right
  rw [← gm₁] at hP hz
  obtain ⟨c₂, k₂, e₂, hk₂, h1, h2, h3, h4, gm₂, gn₂, gr₂, grm₂, go₂⟩ :=
    enOrb_core (P := P) c₁ hw₁ 4678 g0 g1 g2 g3 g4 hP
      (fun u hu h => by omega) (fun u hu h => by omega) (by omega)
      (fun a h h' => hz a (by omega) (by omega)) (by omega) (by omega) (by omega) (by omega)
  refine ⟨c₂, k₁ + k₂, .seq e₁ e₂, by omega, fun i hi j hj => ?_, h2, h3, h4,
    fun a ha hb => ?_, fun x hx hx' => ?_, by rw [gr₂, gr₁], by rw [grm₂, grm₁],
    by rw [go₂, go₁]⟩
  · rw [h1 i hi j hj, gm₁]
  · rw [gm₂ a (fun h => ha ⟨by omega, by omega⟩) (fun h => hb ⟨h.1, by omega⟩), gm₁]
  · rw [gn₂ x hx hx', gn₁ x hx]

theorem enO2_exec (c : Config) (hc : WordsBounded W c) {m B₀ Sb : ℕ}
    (r60 : c.nreg 4660 = m) (r68 : c.nreg 4668 = B₀ + m) (r69 : c.nreg 4669 = B₀ + 2 * m)
    (r76 : c.nreg 4676 = Sb + 7 * m + 3) (r71 : c.nreg 4671 = B₀ + 4 * m)
    (hP : PermArr (fun u => c.nmem (B₀ + m + u)) (fun u => c.nmem (B₀ + 2 * m + u)) m)
    (lay : B₀ + 7 * m ≤ Sb) (w : Sb + 13 * m + 6 ≤ W)
    (hz : ∀ a, Sb + 7 * m + 3 ≤ a → a < Sb + 13 * m + 6 → c.nmem a = 0) :
    ∃ c' k, Exec P W enO2 c c' k ∧ k ≤ 85 * m + 43 ∧
      (∀ i < m, ∀ j < m, (c'.nmem (B₀ + 4 * m + i) = c'.nmem (B₀ + 4 * m + j) ↔
        ∃ k, (fun u => c.nmem (B₀ + m + u))^[k] i = j)) ∧
      (∀ j < m, c'.nmem (B₀ + 4 * m + j) < c'.nreg 4679) ∧
      (∀ r < c'.nreg 4679, ∃ j < m, c'.nmem (B₀ + 4 * m + j) = r) ∧ c'.nreg 4679 ≤ m ∧
      (∀ a, ¬ (Sb + 7 * m + 3 ≤ a ∧ a < Sb + 13 * m + 6) →
        ¬ (B₀ + 4 * m ≤ a ∧ a < B₀ + 5 * m) → c'.nmem a = c.nmem a) ∧
      (∀ x, 4659 < x → x ≠ 4679 → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold enO2
  obtain ⟨c₁, k₁, e₁, hk₁, g0, g1, g2, g3, g4, gn₁, gm₁, gr₁, grm₁, go₁⟩ : ∃ c₁ k₁,
      Exec P W (block [.copyN 4650 4660, .copyN 4651 4668, .copyN 4652 4669, .copyN 4653 4676,
        .copyN 4654 4671]) c c₁ k₁ ∧ k₁ = 5 ∧ c₁.nreg 4650 = m ∧ c₁.nreg 4651 = B₀ + m ∧
      c₁.nreg 4652 = B₀ + 2 * m ∧ c₁.nreg 4653 = Sb + 7 * m + 3 ∧ c₁.nreg 4654 = B₀ + 4 * m ∧
      (∀ x, 4659 < x → c₁.nreg x = c.nreg x) ∧
      c₁.nmem = c.nmem ∧ c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    exec_block
    all_goals try omega
    all_goals try (first | (config_simp; done) | (config_simp; simp only [r60, r68, r69, r76, r71] <;> omega))
    refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
    all_goals try (first | (config_simp; done) | (config_simp; simp only [r60, r68, r69, r76, r71] <;> omega))
    obtain ⟨a1, a2, a3, a4, a5⟩ : x ≠ 4650 ∧ x ≠ 4651 ∧ x ≠ 4652 ∧ x ≠ 4653 ∧ x ≠ 4654 := by
      omega
    simp only [Config.nreg_mk, upd_other _ _ _ a1, upd_other _ _ _ a2, upd_other _ _ _ a3,
      upd_other _ _ _ a4, upd_other _ _ _ a5]
  have hw₁ := e₁.wb_right
  rw [← gm₁] at hP hz
  obtain ⟨c₂, k₂, e₂, hk₂, h1, h2, h3, h4, gm₂, gn₂, gr₂, grm₂, go₂⟩ :=
    enOrb_core (P := P) c₁ hw₁ 4679 g0 g1 g2 g3 g4 hP
      (fun u hu h => by omega) (fun u hu h => by omega) (by omega)
      (fun a h h' => hz a (by omega) (by omega)) (by omega) (by omega) (by omega) (by omega)
  refine ⟨c₂, k₁ + k₂, .seq e₁ e₂, by omega, fun i hi j hj => ?_, h2, h3, h4,
    fun a ha hb => ?_, fun x hx hx' => ?_, by rw [gr₂, gr₁], by rw [grm₂, grm₁],
    by rw [go₂, go₁]⟩
  · rw [h1 i hi j hj, gm₁]
  · rw [gm₂ a (fun h => ha ⟨by omega, by omega⟩) (fun h => hb ⟨h.1, by omega⟩), gm₁]
  · rw [gn₂ x hx hx', gn₁ x hx]

theorem enA1_exec (c : Config) (hc : WordsBounded W c) {m nV B₀ EXb : ℕ}
    (r60 : c.nreg 4660 = m) (r70 : c.nreg 4670 = B₀ + 3 * m) (r63 : c.nreg 4663 = EXb)
    (r67 : c.nreg 4667 = 1) (r72 : c.nreg 4672 = B₀ + 5 * m)
    (hkey : ∀ j < m, c.nmem (B₀ + 3 * m + j) < nV) (hnV : nV ≤ m)
    (hz : ∀ k < nV, c.nmem (B₀ + 5 * m + k) = 0) (lay : B₀ + 7 * m ≤ EXb) (w : EXb + m ≤ W)
    (hW1 : m + 1 ≤ W) (hsum : ∑ j ∈ range m, c.nmem (EXb + j) ≤ W) :
    ∃ c' k, Exec P W enA1 c c' k ∧ k ≤ 12 * m + 9 ∧
      (∀ k < nV, c'.nmem (B₀ + 5 * m + k) =
        saF (fun j => c.nmem (B₀ + 3 * m + j)) (fun j => c.nmem (EXb + j)) m k) ∧
      (∀ a, ¬ (B₀ + 5 * m ≤ a ∧ a < B₀ + 5 * m + nV) → c'.nmem a = c.nmem a) ∧
      (∀ x, 4659 < x → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold enA1
  obtain ⟨c₁, k₁, e₁, hk₁, g0, g1, g2, g3, g4, gn₁, gm₁, gr₁, grm₁, go₁⟩ : ∃ c₁ k₁,
      Exec P W (block [.copyN 4630 4660, .copyN 4631 4670, .copyN 4632 4663, .copyN 4633 4667,
        .copyN 4634 4672]) c c₁ k₁ ∧ k₁ = 5 ∧ c₁.nreg 4630 = m ∧ c₁.nreg 4631 = B₀ + 3 * m ∧
      c₁.nreg 4632 = EXb ∧ c₁.nreg 4633 = 1 ∧ c₁.nreg 4634 = B₀ + 5 * m ∧
      (∀ x, 4659 < x → c₁.nreg x = c.nreg x) ∧
      c₁.nmem = c.nmem ∧ c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    exec_block
    all_goals try omega
    all_goals try (first | (config_simp; done) | (config_simp; simp only [r60, r70, r63, r67, r72] <;> omega))
    refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
    all_goals try (first | (config_simp; done) | (config_simp; simp only [r60, r70, r63, r67, r72] <;> omega))
    obtain ⟨a1, a2, a3, a4, a5⟩ : x ≠ 4630 ∧ x ≠ 4631 ∧ x ≠ 4632 ∧ x ≠ 4633 ∧ x ≠ 4634 := by
      omega
    simp only [Config.nreg_mk, upd_other _ _ _ a1, upd_other _ _ _ a2, upd_other _ _ _ a3,
      upd_other _ _ _ a4, upd_other _ _ _ a5]
  have hw₁ := e₁.wb_right
  have hv : ∀ j, c₁.nmem (EXb + 1 * j) = c.nmem (EXb + j) := fun j => by rw [one_mul, gm₁]
  obtain ⟨c₂, k₂, e₂, hk₂, h1, gm₂, gn₂, gr₂, grm₂, go₂⟩ :=
    saProg_exec (P := P) c₁ hw₁ (nk := nV) g0 g1 g2 g3 g4
      (fun j hj => by rw [gm₁]; exact hkey j hj) (fun k hk => by rw [gm₁]; exact hz k hk)
      (fun j hj h => by omega) (fun j hj h => by omega) (by omega) (by omega)
      (fun j hj => by omega) (by omega) (by simp only [hv]; exact hsum)
  refine ⟨c₂, k₁ + k₂, .seq e₁ e₂, by omega, fun k hk => ?_, fun a ha => ?_,
    fun x hx => ?_, by rw [gr₂, gr₁], by rw [grm₂, grm₁], by rw [go₂, go₁]⟩
  · rw [h1 k hk]; simp only [hv, gm₁]
  · rw [gm₂ a ha, gm₁]
  · rw [gn₂ x (by omega), gn₁ x hx]

theorem enA2_exec (c : Config) (hc : WordsBounded W c) {m nV nF B₀ ONE : ℕ}
    (r60 : c.nreg 4660 = m) (r71 : c.nreg 4671 = B₀ + 4 * m) (r72 : c.nreg 4672 = B₀ + 5 * m)
    (r77 : c.nreg 4677 = ONE) (r78 : c.nreg 4678 = nV) (hone : c.nmem ONE = 1)
    (hkey : ∀ j < m, c.nmem (B₀ + 4 * m + j) < nF) (hn : nV + nF ≤ 2 * m)
    (hz : ∀ k < nF, c.nmem (B₀ + 5 * m + nV + k) = 0) (lay : B₀ + 7 * m ≤ ONE)
    (w : ONE + 1 ≤ W) (hW1 : m + 1 ≤ W) :
    ∃ c' k, Exec P W enA2 c c' k ∧ k ≤ 12 * m + 11 ∧
      (∀ k < nF, c'.nmem (B₀ + 5 * m + nV + k) =
        saF (fun j => c.nmem (B₀ + 4 * m + j)) (fun _ => 1) m k) ∧
      (∀ a, ¬ (B₀ + 5 * m + nV ≤ a ∧ a < B₀ + 5 * m + nV + nF) → c'.nmem a = c.nmem a) ∧
      (∀ x, 4659 < x → x < 4681 → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold enA2
  obtain ⟨c₁, k₁, e₁, hk₁, g0, g1, g2, g3, g4, gn₁, gm₁, gr₁, grm₁, go₁⟩ : ∃ c₁ k₁,
      Exec P W (block [.constN 4681 0, .addN 4682 4672 4678, .copyN 4630 4660,
        .copyN 4631 4671, .copyN 4632 4677, .copyN 4633 4681, .copyN 4634 4682]) c c₁ k₁ ∧
      k₁ = 7 ∧ c₁.nreg 4630 = m ∧ c₁.nreg 4631 = B₀ + 4 * m ∧
      c₁.nreg 4632 = ONE ∧ c₁.nreg 4633 = 0 ∧ c₁.nreg 4634 = B₀ + 5 * m + nV ∧
      (∀ x, 4659 < x → x < 4681 → c₁.nreg x = c.nreg x) ∧
      c₁.nmem = c.nmem ∧ c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    exec_block
    all_goals try omega
    all_goals try (first | (config_simp; done) | (config_simp; simp only [r60, r71, r72, r77, r78] <;> omega))
    refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, fun x hx hx' => ?_, rfl, rfl, rfl, rfl⟩
    all_goals try (first | (config_simp; done) | (config_simp; simp only [r60, r71, r72, r77, r78] <;> omega))
    obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ : x ≠ 4681 ∧ x ≠ 4682 ∧ x ≠ 4630 ∧ x ≠ 4631 ∧
        x ≠ 4632 ∧ x ≠ 4633 ∧ x ≠ 4634 := by omega
    simp only [Config.nreg_mk, upd_other _ _ _ a1, upd_other _ _ _ a2, upd_other _ _ _ a3,
      upd_other _ _ _ a4, upd_other _ _ _ a5, upd_other _ _ _ a6, upd_other _ _ _ a7]
  have hw₁ := e₁.wb_right
  have hv : ∀ j, c₁.nmem (ONE + 0 * j) = 1 := fun j => by rw [zero_mul, Nat.add_zero, gm₁, hone]
  have hsum : ∑ j ∈ range m, c₁.nmem (ONE + 0 * j) ≤ W := by
    simp only [hv, sum_const, card_range, smul_eq_mul, mul_one]; omega
  obtain ⟨c₂, k₂, e₂, hk₂, h1, gm₂, gn₂, gr₂, grm₂, go₂⟩ :=
    saProg_exec (P := P) c₁ hw₁ (nk := nF) g0 g1 g2 g3 g4
      (fun j hj => by rw [gm₁]; exact hkey j hj) (fun k hk => by rw [gm₁]; exact hz k hk)
      (fun j hj h => by omega) (fun j hj h => by omega) (by omega) (by omega)
      (fun j hj => by omega) (by omega) hsum
  refine ⟨c₂, k₁ + k₂, .seq e₁ e₂, by omega, fun k hk => ?_, fun a ha => ?_,
    fun x hx hx' => ?_, by rw [gr₂, gr₁], by rw [grm₂, grm₁], by rw [go₂, go₁]⟩
  · rw [h1 k hk]; simp only [hv, gm₁]
  · rw [gm₂ a ha, gm₁]
  · rw [gn₂ x (by omega), gn₁ x hx hx']

theorem enFin_exec (c : Config) (hc : WordsBounded W c) :
    ∃ c' k, Exec P W enFin c c' k ∧ k = 4 ∧ c'.nreg 390 = c.nreg 4660 ∧
      c'.nreg 391 = c.nreg 4678 ∧ c'.nreg 392 = c.nreg 4679 ∧ c'.nreg 393 = c.nreg 4661 ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold enFin
  exec_block
  all_goals try exact hc.1 _
  all_goals try (config_simp; exact hc.1 _)
  refine ⟨rfl, ?_, ?_, ?_, ?_, rfl, rfl, rfl, rfl⟩ <;> config_simp

end Stages

/-- The steps of `encProg`. -/
abbrev encT (m : ℕ) : ℕ := 217 * m + 160

section Main

variable {P : Input} {W : ℕ}

set_option maxHeartbeats 1600000 in
/-- **The plain encoding of a piece map on the machine.** From the index arrays `REV` at `B₀`
(an involution of `[0, m)`), `SIG` at `SIGb` (a permutation of `[0, m)`), `EX` at `EXb`, laid
out `B₀ + 7m ≤ SIGb`, `SIGb + m ≤ EXb`, `EXb + m ≤ Sb`, `Sb + 13m + 7 ≤ W`, with the weight part
`[B₀ + 5m, B₀ + 7m)` and the scratch `[Sb, Sb + 13m + 7)` zero and `Σ EX ≤ W`: within
`encT m = 217 m + 160` steps the memory holds `φ = SIG ∘ REV` at `B₀ + m`, its inverse at
`B₀ + 2m`, vertex numbers `VN` at `B₀ + 3m` (equal iff in one orbit of `SIG`, onto
`[0, nV)`), face numbers `FN` at `B₀ + 4m` (orbits of `φ`, onto `[0, nF)`), the vertex weights
`Σ_{VN j = k} EX j` at `B₀ + 5m + k`, the face weights `#{j | FN j = k}` at `B₀ + 5m + nV + k`,
and `r390 … r393 = m, nV, nF, B₀`; `REV`, `SIG`, `EX` kept. -/
theorem encProg_exec (c : Config) (hc : WordsBounded W c) {m B₀ SIGb EXb Sb : ℕ}
    (r60 : c.nreg 4660 = m) (r61 : c.nreg 4661 = B₀) (r62 : c.nreg 4662 = SIGb)
    (r63 : c.nreg 4663 = EXb) (r64 : c.nreg 4664 = Sb)
    (lay : B₀ + 7 * m ≤ SIGb ∧ SIGb + m ≤ EXb ∧ EXb + m ≤ Sb ∧ Sb + 13 * m + 7 ≤ W)
    (hR : PermArr (fun u => c.nmem (B₀ + u)) (fun u => c.nmem (B₀ + u)) m)
    (hSl : ∀ j < m, c.nmem (SIGb + j) < m)
    (hSi : ∀ i < m, ∀ j < m, c.nmem (SIGb + i) = c.nmem (SIGb + j) → i = j)
    (hz5 : ∀ a, B₀ + 5 * m ≤ a → a < B₀ + 7 * m → c.nmem a = 0)
    (hzS : ∀ a, Sb ≤ a → a < Sb + 13 * m + 7 → c.nmem a = 0)
    (hsum : ∑ j ∈ range m, c.nmem (EXb + j) ≤ W) :
    ∃ c' k, Exec P W encProg c c' k ∧ k ≤ encT m ∧
      (∀ j < m, c'.nmem (B₀ + j) = c.nmem (B₀ + j)) ∧
      (∀ j < m, c'.nmem (B₀ + m + j) = c.nmem (SIGb + c.nmem (B₀ + j))) ∧
      (∀ j < m, c'.nmem (B₀ + 2 * m + c.nmem (SIGb + c.nmem (B₀ + j))) = j) ∧
      (∀ i < m, ∀ j < m, (c'.nmem (B₀ + 3 * m + i) = c'.nmem (B₀ + 3 * m + j) ↔
        ∃ k, (fun u => c.nmem (SIGb + u))^[k] i = j)) ∧
      (∀ j < m, c'.nmem (B₀ + 3 * m + j) < c'.nreg 391) ∧
      (∀ r < c'.nreg 391, ∃ j < m, c'.nmem (B₀ + 3 * m + j) = r) ∧
      (∀ i < m, ∀ j < m, (c'.nmem (B₀ + 4 * m + i) = c'.nmem (B₀ + 4 * m + j) ↔
        ∃ k, (fun u => c.nmem (SIGb + c.nmem (B₀ + u)))^[k] i = j)) ∧
      (∀ j < m, c'.nmem (B₀ + 4 * m + j) < c'.nreg 392) ∧
      (∀ r < c'.nreg 392, ∃ j < m, c'.nmem (B₀ + 4 * m + j) = r) ∧
      (∀ k < c'.nreg 391, c'.nmem (B₀ + 5 * m + k) =
        saF (fun j => c'.nmem (B₀ + 3 * m + j)) (fun j => c.nmem (EXb + j)) m k) ∧
      (∀ k < c'.nreg 392, c'.nmem (B₀ + 5 * m + c'.nreg 391 + k) =
        saF (fun j => c'.nmem (B₀ + 4 * m + j)) (fun _ => 1) m k) ∧
      c'.nreg 390 = m ∧ c'.nreg 393 = B₀ ∧ c'.nreg 391 ≤ m ∧ c'.nreg 392 ≤ m ∧
      (∀ a, ¬ (B₀ + m ≤ a ∧ a < B₀ + 7 * m) → ¬ (Sb ≤ a ∧ a < Sb + 13 * m + 7) →
        c'.nmem a = c.nmem a) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨l1, l2, l3, l4⟩ := lay
  have hW1 : m + 1 ≤ W := by omega
  set m₀ := c.nmem with hm₀
  -- 1. addresses
  obtain ⟨c₁, k₁, e₁, hk₁, s67, s68, s69, s70, s71, s72, s73, s76, s77, gm₁, gn₁, gr₁, grm₁,
    go₁⟩ := enSet_exec (P := P) c hc r60 r61 r64 (by omega) l4
  have hw₁ := e₁.wb_right
  have f1 : ∀ a, a ≠ Sb + 13 * m + 6 → c₁.nmem a = m₀ a := fun a ha => by
    rw [gm₁, upd_other _ _ _ ha]
  have q1 : ∀ x, 4659 < x → x < 4667 → c₁.nreg x = c.nreg x := fun x a b => gn₁ x (by omega)
  -- 2. φ
  obtain ⟨c₂, k₂, e₂, hk₂, h₂, gm₂, gn₂, gr₂, grm₂, go₂⟩ := enGa_exec (P := P) c₁ hw₁
    (m := m) (B₀ := B₀) (SIGb := SIGb) (by rw [q1 _ (by omega) (by omega), r60])
    (by rw [q1 _ (by omega) (by omega), r61]) (by rw [q1 _ (by omega) (by omega), r62]) s68
    (fun j hj => by rw [f1 _ (by omega)]; exact hR.plt j hj) l1 (by omega) hW1
  have hw₂ := e₂.wb_right
  have hphi : ∀ j < m, c₂.nmem (B₀ + m + j) = m₀ (SIGb + m₀ (B₀ + j)) := fun j hj => by
    rw [h₂ j hj, f1 (B₀ + j) (by omega), f1 _ (by have := hR.plt j hj; omega)]
  have hphil : ∀ j < m, m₀ (SIGb + m₀ (B₀ + j)) < m := fun j hj => hSl _ (hR.plt j hj)
  have hphii : ∀ i < m, ∀ j < m, m₀ (SIGb + m₀ (B₀ + i)) = m₀ (SIGb + m₀ (B₀ + j)) → i = j :=
    fun i hi j hj e => by
      have := hSi _ (hR.plt i hi) _ (hR.plt j hj) e
      rw [← hR.left i hi, ← hR.left j hj]; exact congrArg (fun u => m₀ (B₀ + u)) this
  have f2 : ∀ a, ¬ (B₀ + m ≤ a ∧ a < B₀ + 2 * m) → a ≠ Sb + 13 * m + 6 → c₂.nmem a = m₀ a :=
    fun a ha hb => by rw [gm₂ a ha, f1 a hb]
  -- 3. φ⁻¹
  obtain ⟨c₃, k₃, e₃, hk₃, h₃, gm₃, gn₃, gr₃, grm₃, go₃⟩ := enI1_exec (P := P) c₂ hw₂
    (m := m) (B₀ := B₀) (by rw [gn₂ _ (by omega), q1 _ (by omega) (by omega), r60])
    (by rw [gn₂ _ (by omega), s68]) (by rw [gn₂ _ (by omega), s69])
    (fun j hj => by rw [hphi j hj]; exact hphil j hj)
    (fun i hi j hj e => hphii i hi j hj (by rw [← hphi i hi, ← hphi j hj]; exact e))
    (by omega) hW1
  have hw₃ := e₃.wb_right
  have hpi : ∀ j < m, c₃.nmem (B₀ + 2 * m + m₀ (SIGb + m₀ (B₀ + j))) = j := fun j hj => by
    rw [← hphi j hj]; exact h₃ j hj
  -- 4. SIG⁻¹
  have q3 : ∀ x, 4659 < x → c₃.nreg x = c₁.nreg x := fun x hx => by rw [gn₃ x hx, gn₂ x hx]
  have f3 : ∀ a, ¬ (B₀ + m ≤ a ∧ a < B₀ + 3 * m) → a ≠ Sb + 13 * m + 6 → c₃.nmem a = m₀ a :=
    fun a ha hb => by
      rw [gm₃ a (fun h => ha ⟨by omega, h.2⟩), f2 a (fun h => ha ⟨h.1, by omega⟩) hb]
  obtain ⟨c₄, k₄, e₄, hk₄, h₄, gm₄, gn₄, gr₄, grm₄, go₄⟩ := enI2_exec (P := P) c₃ hw₃
    (m := m) (SIGb := SIGb) (Sb := Sb) (by rw [q3 _ (by omega), q1 _ (by omega) (by omega), r60])
    (by rw [q3 _ (by omega), q1 _ (by omega) (by omega), r62])
    (by rw [q3 _ (by omega), q1 _ (by omega) (by omega), r64])
    (fun j hj => by rw [f3 _ (by omega) (by omega)]; exact hSl j hj)
    (fun i hi j hj e => hSi i hi j hj (by
      rwa [f3 _ (by omega) (by omega), f3 _ (by omega) (by omega)] at e)) (by omega) (by omega) hW1
  have hw₄ := e₄.wb_right
  have q4 : ∀ x, 4659 < x → c₄.nreg x = c₁.nreg x := fun x hx => by rw [gn₄ x hx, q3 x hx]
  have f4 : ∀ a, ¬ (B₀ + m ≤ a ∧ a < B₀ + 3 * m) → ¬ (Sb ≤ a ∧ a < Sb + m) →
      a ≠ Sb + 13 * m + 6 → c₄.nmem a = m₀ a := fun a ha hb hc' => by
    rw [gm₄ a hb, f3 a ha hc']
  have hsig4 : ∀ u < m, c₄.nmem (SIGb + u) = m₀ (SIGb + u) := fun u hu =>
    f4 _ (by omega) (by omega) (by omega)
  have hsi4 : ∀ j < m, c₄.nmem (Sb + m₀ (SIGb + j)) = j := fun j hj => by
    have := h₄ j hj
    rwa [f3 (SIGb + j) (by omega) (by omega)] at this
  have hP1 : PermArr (fun u => c₄.nmem (SIGb + u)) (fun u => c₄.nmem (Sb + u)) m := by
    refine permArr_of_inv (fun u hu => by rw [hsig4 u hu]; exact hSl u hu)
      (fun i hi j hj e => hSi i hi j hj (by rwa [hsig4 i hi, hsig4 j hj] at e))
      (fun j hj => ?_)
    simp only [hsig4 j hj]; exact hsi4 j hj
  -- 5. vertex numbers
  obtain ⟨c₅, k₅, e₅, hk₅, v1, v2, v3, v4, gm₅, gn₅, gr₅, grm₅, go₅⟩ := enO1_exec (P := P)
    c₄ hw₄ (m := m) (B₀ := B₀) (SIGb := SIGb) (Sb := Sb)
    (by rw [q4 _ (by omega), q1 _ (by omega) (by omega), r60])
    (by rw [q4 _ (by omega), q1 _ (by omega) (by omega), r62])
    (by rw [q4 _ (by omega), q1 _ (by omega) (by omega), r64])
    (by rw [q4 _ (by omega), s73]) (by rw [q4 _ (by omega), s70]) hP1 (by omega) (by omega) (by omega)
    (fun a h1 h2 => by rw [f4 a (by omega) (by omega) (by omega)]; exact hzS a (by omega) (by omega))
  have hw₅ := e₅.wb_right
  set nV := c₅.nreg 4678 with hnV
  have q5 : ∀ x, 4659 < x → x ≠ 4678 → c₅.nreg x = c₁.nreg x := fun x hx hx' => by
    rw [gn₅ x hx hx', q4 x hx]
  -- 6. face numbers
  have hphi5 : ∀ u < m, c₅.nmem (B₀ + m + u) = m₀ (SIGb + m₀ (B₀ + u)) := fun u hu => by
    rw [gm₅ _ (by omega) (by omega), gm₄ _ (by omega),
      gm₃ _ (by omega)]; exact hphi u hu
  have hpi5 : ∀ j < m, c₅.nmem (B₀ + 2 * m + m₀ (SIGb + m₀ (B₀ + j))) = j := fun j hj => by
    have := hphil j hj
    rw [gm₅ _ (by omega) (by omega), gm₄ _ (by omega)]; exact hpi j hj
  have hP2 : PermArr (fun u => c₅.nmem (B₀ + m + u)) (fun u => c₅.nmem (B₀ + 2 * m + u)) m := by
    refine permArr_of_inv (fun u hu => by rw [hphi5 u hu]; exact hphil u hu)
      (fun i hi j hj e => hphii i hi j hj (by rwa [hphi5 i hi, hphi5 j hj] at e))
      (fun j hj => ?_)
    simp only [hphi5 j hj]; exact hpi5 j hj
  obtain ⟨c₆, k₆, e₆, hk₆, u1, u2, u3, u4, gm₆, gn₆, gr₆, grm₆, go₆⟩ := enO2_exec (P := P)
    c₅ hw₅ (m := m) (B₀ := B₀) (Sb := Sb)
    (by rw [q5 _ (by omega) (by omega), q1 _ (by omega) (by omega), r60])
    (by rw [q5 _ (by omega) (by omega), s68]) (by rw [q5 _ (by omega) (by omega), s69])
    (by rw [q5 _ (by omega) (by omega), s76]) (by rw [q5 _ (by omega) (by omega), s71]) hP2
    (by omega) (by omega)
    (fun a h1 h2 => by
      rw [gm₅ a (by omega) (by omega), f4 a (by omega) (by omega) (by omega)]
      exact hzS a (by omega) (by omega))
  have hw₆ := e₆.wb_right
  set nF := c₆.nreg 4679 with hnF
  have q6 : ∀ x, 4659 < x → x ≠ 4678 → x ≠ 4679 → c₆.nreg x = c₁.nreg x :=
    fun x hx hx' hx'' => by rw [gn₆ x hx hx'', q5 x hx hx']
  have hnV6 : c₆.nreg 4678 = nV := gn₆ _ (by omega) (by omega)
  -- 7. vertex weights
  have hvn6 : ∀ j < m, c₆.nmem (B₀ + 3 * m + j) = c₅.nmem (B₀ + 3 * m + j) := fun j hj =>
    gm₆ _ (by omega) (by omega)
  have f6 : ∀ a, ¬ (B₀ + m ≤ a ∧ a < B₀ + 7 * m) → ¬ (Sb ≤ a ∧ a < Sb + 13 * m + 7) →
      c₆.nmem a = m₀ a := fun a ha hb => by
    rw [gm₆ a (by omega) (by omega), gm₅ a (by omega) (by omega),
      f4 a (by omega) (by omega) (by omega)]
  have f6' : ∀ a, B₀ + 5 * m ≤ a → a < B₀ + 7 * m → c₆.nmem a = m₀ a := fun a ha hb => by
    rw [gm₆ a (by omega) (by omega), gm₅ a (by omega) (by omega),
      f4 a (by omega) (by omega) (by omega)]
  obtain ⟨c₇, k₇, e₇, hk₇, w₇, gm₇, gn₇, gr₇, grm₇, go₇⟩ := enA1_exec (P := P) c₆ hw₆
    (m := m) (nV := nV) (B₀ := B₀) (EXb := EXb)
    (by rw [q6 _ (by omega) (by omega) (by omega), q1 _ (by omega) (by omega), r60])
    (by rw [q6 _ (by omega) (by omega) (by omega), s70])
    (by rw [q6 _ (by omega) (by omega) (by omega), q1 _ (by omega) (by omega), r63])
    (by rw [q6 _ (by omega) (by omega) (by omega), s67])
    (by rw [q6 _ (by omega) (by omega) (by omega), s72])
    (fun j hj => by rw [hvn6 j hj]; exact v2 j hj) v4
    (fun k hk => by rw [f6' _ (by omega) (by omega)]; exact hz5 _ (by omega) (by omega))
    (by omega) (by omega) hW1
    (by
      have : ∀ j ∈ range m, c₆.nmem (EXb + j) = m₀ (EXb + j) := fun j hj => by
        have := mem_range.1 hj; exact f6 _ (by omega) (by omega)
      rw [sum_congr rfl this]; exact hsum)
  have hw₇ := e₇.wb_right
  have q7 : ∀ x, 4659 < x → c₇.nreg x = c₆.nreg x := gn₇
  -- 8. face weights
  have hfn7 : ∀ j < m, c₇.nmem (B₀ + 4 * m + j) = c₆.nmem (B₀ + 4 * m + j) := fun j hj =>
    gm₇ _ (by omega)
  have hone : c₇.nmem (Sb + 13 * m + 6) = 1 := by
    rw [gm₇ _ (by omega), gm₆ _ (by omega) (by omega), gm₅ _ (by omega) (by omega),
      gm₄ _ (by omega), gm₃ _ (by omega), gm₂ _ (by omega), gm₁, upd_same]
  obtain ⟨c₈, k₈, e₈, hk₈, w₈, gm₈, gn₈, gr₈, grm₈, go₈⟩ := enA2_exec (P := P) c₇ hw₇
    (m := m) (nV := nV) (nF := nF) (B₀ := B₀) (ONE := Sb + 13 * m + 6)
    (by rw [q7 _ (by omega), q6 _ (by omega) (by omega) (by omega), q1 _ (by omega) (by omega),
      r60])
    (by rw [q7 _ (by omega), q6 _ (by omega) (by omega) (by omega), s71])
    (by rw [q7 _ (by omega), q6 _ (by omega) (by omega) (by omega), s72])
    (by rw [q7 _ (by omega), q6 _ (by omega) (by omega) (by omega), s77])
    (by rw [q7 _ (by omega), hnV6]) hone
    (fun j hj => by rw [hfn7 j hj]; exact u2 j hj) (by omega)
    (fun k hk => by
      rw [gm₇ _ (by omega), f6' _ (by omega) (by omega)]; exact hz5 _ (by omega) (by omega))
    (by omega) (by omega) hW1
  have hw₈ := e₈.wb_right
  -- 9. the registers of `msep`
  obtain ⟨c₉, k₉, e₉, hk₉, t0, t1, t2, t3, gm₉, gr₉, grm₉, go₉⟩ := enFin_exec (P := P) c₈ hw₈
  have q8 : ∀ x, 4659 < x → x < 4681 → c₈.nreg x = c₆.nreg x := fun x hx hx' => by
    rw [gn₈ x hx hx', q7 x hx]
  have t1' : c₉.nreg 391 = nV := by rw [t1, q8 _ (by omega) (by omega), hnV6]
  have t2' : c₉.nreg 392 = nF := by rw [t2, q8 _ (by omega) (by omega)]
  -- the memory at the end
  have m8 : ∀ a, ¬ (B₀ + 5 * m ≤ a ∧ a < B₀ + 7 * m) → c₉.nmem a = c₆.nmem a := fun a ha => by
    rw [gm₉, gm₈ a (by omega), gm₇ a (by omega)]
  have hvn9 : ∀ j < m, c₉.nmem (B₀ + 3 * m + j) = c₅.nmem (B₀ + 3 * m + j) := fun j hj => by
    rw [m8 _ (by omega), hvn6 j hj]
  have hfn9 : ∀ j < m, c₉.nmem (B₀ + 4 * m + j) = c₆.nmem (B₀ + 4 * m + j) := fun j hj => by
    rw [m8 _ (by omega)]
  refine ⟨c₉, k₁ + (k₂ + (k₃ + (k₄ + (k₅ + (k₆ + (k₇ + (k₈ + k₉))))))),
    .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ (.seq e₅ (.seq e₆ (.seq e₇ (.seq e₈ e₉))))))),
    by unfold encT; omega, fun j hj => ?_, fun j hj => ?_, fun j hj => ?_,
    fun i hi j hj => ?_, fun j hj => ?_, fun r hr => ?_, fun i hi j hj => ?_,
    fun j hj => ?_, fun r hr => ?_, fun k hk => ?_, fun k hk => ?_, ?_, ?_, ?_, ?_,
    fun a ha hb => ?_, ?_, ?_, ?_⟩
  · rw [m8 _ (by omega), f6 _ (by omega) (by omega)]
  · rw [m8 _ (by omega), gm₆ _ (by omega) (by omega)]; exact hphi5 j hj
  · have := hphil j hj
    rw [m8 _ (by omega), gm₆ _ (by omega) (by omega)]; exact hpi5 j hj
  · rw [hvn9 i hi, hvn9 j hj, v1 i hi j hj]
    have e : ∀ k, (fun u => c₄.nmem (SIGb + u))^[k] i = (fun u => m₀ (SIGb + u))^[k] i :=
      fun k => iter_congr (fun u hu => by rw [hsig4 u hu]; exact hSl u hu) hsig4 k hi
    simp only [e]
  · rw [hvn9 j hj, t1']; exact v2 j hj
  · rw [t1'] at hr; obtain ⟨j, hj, e⟩ := v3 r hr; exact ⟨j, hj, by rw [hvn9 j hj]; exact e⟩
  · rw [hfn9 i hi, hfn9 j hj, u1 i hi j hj]
    have e : ∀ k, (fun u => c₅.nmem (B₀ + m + u))^[k] i =
        (fun u => m₀ (SIGb + m₀ (B₀ + u)))^[k] i :=
      fun k => iter_congr (fun u hu => by rw [hphi5 u hu]; exact hphil u hu) hphi5 k hi
    simp only [e]
  · rw [hfn9 j hj, t2']; exact u2 j hj
  · rw [t2'] at hr; obtain ⟨j, hj, e⟩ := u3 r hr; exact ⟨j, hj, by rw [hfn9 j hj]; exact e⟩
  · rw [t1'] at hk
    rw [gm₉, gm₈ _ (by omega), w₇ k hk]
    exact saF_congr (fun j hj => by rw [hvn6 j hj, ← hvn9 j hj, gm₉])
      (fun j hj => f6 _ (by omega) (by omega)) k
  · rw [t2'] at hk
    rw [gm₉, t1', w₈ k hk]
    exact saF_congr (fun j hj => by rw [hfn7 j hj, ← hfn9 j hj, gm₉]) (fun _ _ => rfl) k
  · rw [t0, q8 _ (by omega) (by omega), q6 _ (by omega) (by omega) (by omega),
      q1 _ (by omega) (by omega), r60]
  · rw [t3, q8 _ (by omega) (by omega), q6 _ (by omega) (by omega) (by omega),
      q1 _ (by omega) (by omega), r61]
  · rw [t1']; exact v4
  · rw [t2']; exact u4
  · rw [m8 _ (by omega), f6 a ha hb]
  · rw [gr₉, gr₈, gr₇, gr₆, gr₅, gr₄, gr₃, gr₂, gr₁]
  · rw [grm₉, grm₈, grm₇, grm₆, grm₅, grm₄, grm₃, grm₂, grm₁]
  · rw [go₉, go₈, go₇, go₆, go₅, go₄, go₃, go₂, go₁]

end Main

end BKMNW

end PlanarFlow
