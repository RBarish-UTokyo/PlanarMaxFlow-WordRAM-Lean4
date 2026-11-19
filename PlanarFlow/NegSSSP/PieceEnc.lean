module

public import PlanarFlow.NegSSSP.CompProg

/-!
# The plain encoding of the piece map of a component, on the machine

The large-component split (`PlanarFlow.NegSSSP.sep_run_split_full`) starts from the plain encoding
(`PlanarSeparator.MillerProg.Enc`) of the piece map `kmap N K` of the large component `K`: its
darts numbered by an equivalence `c`, the reversal, the face permutation and its inverse, a
vertex number and a face number per dart. Here it is computed from the plain encoding of the
piece carrying its own rotation (`PEnc`) and the flags of `K` that `compProg` leaves.

* `orbProg`: **orbit labelling** of a permutation given by an array: the cycles numbered
  `0, 1, …` in the order of their first element (`orbProg_exec`, `32 n + 8` steps); with
  `exists_equiv_of_lab`, the numbering of the vertices (cycles of the rotation) and of the faces
  (cycles of the face permutation) as equivalences.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace NegSSSP

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs Monge Finset

variable {P : Input} {W : ℕ}

/-! ### Orbit labelling

Registers: `r900 = n`, `r901 = bp` (the permutation at `bp + x`), `r902 = bL` (the labels at
`bL + x`), `r10 = 1`; the program writes `r903 … r908` only: `r903 = n + 1` (the mark of an
unlabelled element), `r904` the scanned element, `r905` the number of labels, `r906` the walked
element, `r907` its label. -/

/-- Marking `bL + r904` unlabelled. -/
def olInit : Stmt := block [.addN 908 902 904, .storeN 908 903, .addN 904 904 10]

/-- One step of the walk of a cycle: label `r906` (at `r908`), move to its image. -/
def olIn : Stmt :=
  block [.storeN 908 905, .addN 908 901 906, .loadN 906 908, .addN 908 902 906, .loadN 907 908]

/-- A new cycle at `r904`: label it, walk the cycle, count the label. -/
def olNew : Stmt :=
  .seq (block [.storeN 908 905, .addN 908 901 904, .loadN 906 908, .addN 908 902 906,
    .loadN 907 908]) (.seq (.whileLtN 900 907 olIn) (.instr (.addN 905 905 10)))

/-- The scan of the element `r904`. -/
def olBody : Stmt :=
  .seq (block [.addN 908 902 904, .loadN 907 908])
    (.seq (.ifLtN 900 907 olNew .skip) (.instr (.addN 904 904 10)))

/-- **Orbit labelling** of the permutation at `bp` on `0, …, n - 1`, labels at `bL`. -/
def orbProg : Stmt :=
  .seq (block [.addN 903 900 10, .constN 904 0]) <| .seq (.whileLtN 904 900 olInit) <|
  .seq (block [.constN 904 0, .constN 905 0]) (.whileLtN 904 900 olBody)

/-- One step of the walk. -/
theorem olIn_exec {bp bL cnt j : ℕ} (c₁ : Config) (hw : WordsBounded W c₁)
    (h901 : c₁.nreg 901 = bp) (h902 : c₁.nreg 902 = bL) (h906 : c₁.nreg 906 = j)
    (h908 : c₁.nreg 908 = bL + j) (h905 : c₁.nreg 905 = cnt) (hne : bp + j ≠ bL + j)
    (w1 : bp + j ≤ W) (w2 : bL + c₁.nmem (bp + j) ≤ W) :
    ∃ c' k, Exec P W olIn c₁ c' k ∧ k = 5 ∧ c'.nmem = upd c₁.nmem (bL + j) cnt ∧
      c'.nreg 906 = c₁.nmem (bp + j) ∧ c'.nreg 908 = bL + c₁.nmem (bp + j) ∧
      c'.nreg 907 = c'.nmem (bL + c₁.nmem (bp + j)) ∧
      (∀ r, r ≠ 906 → r ≠ 907 → r ≠ 908 → c'.nreg r = c₁.nreg r) ∧
      c'.rreg = c₁.rreg ∧ c'.rmem = c₁.rmem ∧ c'.output = c₁.output := by
  unfold olIn
  exec_block
  all_goals try ((try config_simp); (try simp only [h901, h902, h906, h908, upd_apply,
    hne, ↓reduceIte]) <;> omega)
  config_simp
  simp only [h901, h902, h906, h908, h905, upd_apply, hne, ↓reduceIte]
  and_intros
  all_goals first | rfl | trivial | (intro r h1 h2 h3; simp [h1, h2, h3])

/-- The start of a new cycle at `i`. -/
theorem olNewB_exec {bp bL cnt i : ℕ} (c₁ : Config) (hw : WordsBounded W c₁)
    (h901 : c₁.nreg 901 = bp) (h902 : c₁.nreg 902 = bL) (h904 : c₁.nreg 904 = i)
    (h908 : c₁.nreg 908 = bL + i) (h905 : c₁.nreg 905 = cnt) (hne : bp + i ≠ bL + i)
    (w1 : bp + i ≤ W) (w2 : bL + c₁.nmem (bp + i) ≤ W) :
    ∃ c' k, Exec P W (block [.storeN 908 905, .addN 908 901 904, .loadN 906 908,
      .addN 908 902 906, .loadN 907 908]) c₁ c' k ∧ k = 5 ∧
      c'.nmem = upd c₁.nmem (bL + i) cnt ∧
      c'.nreg 906 = c₁.nmem (bp + i) ∧ c'.nreg 908 = bL + c₁.nmem (bp + i) ∧
      c'.nreg 907 = c'.nmem (bL + c₁.nmem (bp + i)) ∧
      (∀ r, r ≠ 906 → r ≠ 907 → r ≠ 908 → c'.nreg r = c₁.nreg r) ∧
      c'.rreg = c₁.rreg ∧ c'.rmem = c₁.rmem ∧ c'.output = c₁.output := by
  exec_block
  all_goals try ((try config_simp); (try simp only [h901, h902, h904, h908, upd_apply,
    hne, ↓reduceIte]) <;> omega)
  config_simp
  simp only [h901, h902, h904, h908, h905, upd_apply, hne, ↓reduceIte]
  and_intros
  all_goals first | rfl | trivial | (intro r h1 h2 h3; simp [h1, h2, h3])

/-- Reading the label of the scanned element. -/
theorem olBodyB_exec {bL i : ℕ} (c₁ : Config) (hw : WordsBounded W c₁)
    (h902 : c₁.nreg 902 = bL) (h904 : c₁.nreg 904 = i) (w1 : bL + i ≤ W) :
    ∃ c' k, Exec P W (block [.addN 908 902 904, .loadN 907 908]) c₁ c' k ∧ k = 2 ∧
      c'.nmem = c₁.nmem ∧ c'.nreg 908 = bL + i ∧ c'.nreg 907 = c₁.nmem (bL + i) ∧
      (∀ r, r ≠ 907 → r ≠ 908 → c'.nreg r = c₁.nreg r) ∧
      c'.rreg = c₁.rreg ∧ c'.rmem = c₁.rmem ∧ c'.output = c₁.output := by
  exec_block
  all_goals try ((try config_simp); (try simp only [h902, h904]) <;> omega)
  config_simp
  simp only [h902, h904, upd_apply]
  and_intros
  all_goals first | rfl | trivial | (intro r h1 h2; simp [h1, h2])

section Orb

variable {T : Type*} [Fintype T] [DecidableEq T] {n : ℕ} (π : Equiv.Perm T) (e : T ≃ Fin n)

open Classical in
/-- The unlabelled elements of the cycle of `t0` (label `n + 1`). -/
noncomputable def cUnl (t0 : T) (bL : ℕ) (mem : ℕ → ℕ) : ℕ :=
  #(univ.filter fun y => π.SameCycle t0 y ∧ mem (bL + e y) = n + 1)

open Classical in
/-- The unlabelled elements (label `n + 1`). -/
noncomputable def aUnl (bL : ℕ) (mem : ℕ → ℕ) : ℕ := #(univ.filter fun y => mem (bL + e y) = n + 1)

variable {π e}

lemma cyc_closed {S : T → Prop} {t0 : T} (h0 : S t0)
    (hs : ∀ y, π.SameCycle t0 y → S y → S (π y)) : ∀ y, π.SameCycle t0 y → S y := by
  intro y hy
  obtain ⟨k, rfl⟩ := hy.exists_nat_pow_eq
  induction k with
  | zero => simpa using h0
  | succ k ih =>
    rw [pow_succ', Equiv.Perm.mul_apply]
    exact hs _ (Equiv.Perm.sameCycle_pow_right.2 (Equiv.Perm.SameCycle.refl _ _))
      (ih (Equiv.Perm.sameCycle_pow_right.2 (Equiv.Perm.SameCycle.refl _ _)))

lemma e_add_inj {bL : ℕ} {y y' : T} (h : bL + (e y : ℕ) = bL + e y') : y = y' :=
  e.injective (Fin.ext (by omega))

lemma cUnl_upd {t0 j : T} {bL v : ℕ} {mem : ℕ → ℕ} (hj : π.SameCycle t0 j)
    (h : mem (bL + e j) = n + 1) (hv : v ≠ n + 1) :
    cUnl π e t0 bL (upd mem (bL + e j) v) + 1 = cUnl π e t0 bL mem := by
  classical
  unfold cUnl
  have : (univ.filter fun y => π.SameCycle t0 y ∧ upd mem (bL + e j) v (bL + e y) = n + 1) =
      (univ.filter fun y => π.SameCycle t0 y ∧ mem (bL + e y) = n + 1).erase j := by
    ext y
    simp only [mem_filter, mem_univ, true_and, mem_erase, upd_apply]
    by_cases hy : y = j
    · subst hy; simp [hv]
    · have : ¬ (e y : ℕ) = e j := fun h' => hy (e.injective (Fin.ext h'))
      simp [this, hy]
  convert card_erase_add_one (s := univ.filter fun y => π.SameCycle t0 y ∧ mem (bL + e y) = n + 1)
    (a := j) (by simp [hj, h])

/-- The state of the walk of the cycle of `t0` at the element `j`, labelled `cnt`, from the
memory `M₀` and the registers of `c₁`. -/
structure WalkJ (W n bL cnt : ℕ) (t0 j : T) (M₀ : ℕ → ℕ) (c₁ c : Config) : Prop where
  wb : WordsBounded W c
  hj : π.SameCycle t0 j
  r906 : c.nreg 906 = e j
  r908 : c.nreg 908 = bL + e j
  r907 : c.nreg 907 = c.nmem (bL + e j)
  reg : ∀ r, r ≠ 906 → r ≠ 907 → r ≠ 908 → c.nreg r = c₁.nreg r
  rreg : c.rreg = c₁.rreg
  rmem : c.rmem = c₁.rmem
  out : c.output = c₁.output
  fr : ∀ a, (∀ y, π.SameCycle t0 y → a ≠ bL + e y) → c.nmem a = M₀ a
  two : ∀ y, π.SameCycle t0 y → c.nmem (bL + e y) = cnt ∨ c.nmem (bL + e y) = n + 1
  t0l : c.nmem (bL + e t0) = cnt
  cl : ∀ y, π.SameCycle t0 y → c.nmem (bL + e y) = cnt →
    c.nmem (bL + e (π y)) = cnt ∨ π y = j

/-- **The walk of a cycle**: from a state of the walk, the inner loop labels the whole cycle of
`t0` with `cnt`, within `7` steps per unlabelled element of the cycle. -/
theorem olWalk_exec {bp bL cnt : ℕ} {t0 j : T} {M₀ : ℕ → ℕ} {c₁ c : Config}
    (hI : WalkJ (π := π) (e := e) W n bL cnt t0 j M₀ c₁ c)
    (h900 : c₁.nreg 900 = n) (h901 : c₁.nreg 901 = bp) (h902 : c₁.nreg 902 = bL)
    (h905 : c₁.nreg 905 = cnt) (hcnt : cnt ≤ n)
    (hp : ∀ t, M₀ (bp + e t) = e (π t)) (hd : bp + n ≤ bL ∨ bL + n ≤ bp)
    (wp : bp + n ≤ W) (wL : bL + n ≤ W) :
    ∃ c' k, Exec P W (.whileLtN 900 907 olIn) c c' k ∧ k ≤ 7 * cUnl π e t0 bL c.nmem + 2 ∧
      (∀ y, π.SameCycle t0 y → c'.nmem (bL + e y) = cnt) ∧
      (∀ a, (∀ y, π.SameCycle t0 y → a ≠ bL + e y) → c'.nmem a = M₀ a) ∧
      (∀ r, r ≠ 906 → r ≠ 907 → r ≠ 908 → c'.nreg r = c₁.nreg r) ∧
      c'.rreg = c₁.rreg ∧ c'.rmem = c₁.rmem ∧ c'.output = c₁.output := by
  refine spec_while (fun c => ∃ j, WalkJ (π := π) (e := e) W n bL cnt t0 j M₀ c₁ c)
    (fun c => 7 * cUnl π e t0 bL c.nmem) (fun c ⟨j, h⟩ => h.wb) ?_ ⟨j, hI⟩ ?_
  · intro c ⟨j, h⟩ hlt
    have hx : c.nmem (bL + e j) = n + 1 := by
      rcases h.two j h.hj with h' | h'
      · rw [h.reg 900 (by omega) (by omega) (by omega), h900, h.r907, h'] at hlt; omega
      · exact h'
    have hpj : c.nmem (bp + e j) = e (π j) := by
      rw [h.fr _ fun y _ => by have := (e y).isLt; have := (e j).isLt; omega]; exact hp j
    have hj' := (e j).isLt
    have hπ := (e (π j)).isLt
    obtain ⟨c', k, hex, hk, hm, h906, h908, h907, hreg, hrr, hrm, ho⟩ :=
      olIn_exec (P := P) c h.wb (by rw [h.reg 901 (by omega) (by omega) (by omega), h901])
        (by rw [h.reg 902 (by omega) (by omega) (by omega), h902]) h.r906 h.r908
        (by rw [h.reg 905 (by omega) (by omega) (by omega), h905]) (by omega) (by omega)
        (by rw [hpj]; omega)
    rw [hpj] at h906 h908 h907
    have hcu := cUnl_upd (π := π) (e := e) (v := cnt) h.hj hx (by omega)
    refine ⟨c', k, hex, ⟨π j, ⟨hex.wb_right, ?_, h906, h908, h907, fun r h1 h2 h3 => ?_,
      hrr.trans h.rreg, hrm.trans h.rmem, ho.trans h.out, fun a ha => ?_, fun y hy => ?_, ?_,
      fun y hy hl => ?_⟩⟩, ?_⟩
    · exact h.hj.trans (Equiv.Perm.sameCycle_apply_right.2 (Equiv.Perm.SameCycle.refl _ _))
    · rw [hreg r h1 h2 h3, h.reg r h1 h2 h3]
    · rw [hm, upd_apply]; simp only [ha j h.hj, ↓reduceIte]; exact h.fr a ha
    · rw [hm, upd_apply]
      split_ifs
      · exact Or.inl rfl
      · exact h.two y hy
    · rw [hm, upd_apply]
      split_ifs
      · rfl
      · exact h.t0l
    · by_cases hyj : y = j
      · subst hyj; exact Or.inr rfl
      · have hne : ¬ bL + (e y : ℕ) = bL + e j := fun h' => hyj (e_add_inj h')
        rw [hm, upd_apply] at hl
        simp only [hne, ↓reduceIte] at hl
        left
        rw [hm, upd_apply]
        split_ifs with h1
        · rfl
        · rcases h.cl y hy hl with h' | h'
          · exact h'
          · exact absurd (by rw [h']) h1
    · rw [hm]; omega
  · intro c' k ⟨j', h⟩ hn hk
    have hlab : c'.nmem (bL + e j') = cnt := by
      rcases h.two j' h.hj with h' | h'
      · exact h'
      · rw [h.reg 900 (by omega) (by omega) (by omega), h900, h.r907, h'] at hn; omega
    refine ⟨hk, cyc_closed (S := fun y => c'.nmem (bL + e y) = cnt) h.t0l (fun y hy hl => ?_),
      h.fr, h.reg, h.rreg, h.rmem, h.out⟩
    rcases h.cl y hy hl with h' | h'
    · exact h'
    · rw [h']; exact hlab

/-- **A new cycle**: from an element `t0` (at `r904`) whose whole cycle is unlabelled, `olNew`
labels the cycle with `cnt` and counts the label, within `7` steps per element of the cycle. -/
theorem olNew_exec {bp bL cnt : ℕ} {t0 : T} {c : Config} (hw : WordsBounded W c)
    (h900 : c.nreg 900 = n) (h901 : c.nreg 901 = bp) (h902 : c.nreg 902 = bL)
    (h904 : c.nreg 904 = e t0) (h905 : c.nreg 905 = cnt) (h908 : c.nreg 908 = bL + e t0)
    (h10 : c.nreg 10 = 1) (hcnt : cnt < n)
    (hun : ∀ y, π.SameCycle t0 y → c.nmem (bL + e y) = n + 1)
    (hp : ∀ t, c.nmem (bp + e t) = e (π t)) (hd : bp + n ≤ bL ∨ bL + n ≤ bp)
    (wp : bp + n ≤ W) (wL : bL + n ≤ W) :
    ∃ c' k, Exec P W olNew c c' k ∧ k ≤ 7 * cUnl π e t0 bL c.nmem + 1 ∧
      1 ≤ cUnl π e t0 bL c.nmem ∧
      (∀ y, π.SameCycle t0 y → c'.nmem (bL + e y) = cnt) ∧
      (∀ a, (∀ y, π.SameCycle t0 y → a ≠ bL + e y) → c'.nmem a = c.nmem a) ∧
      c'.nreg 905 = cnt + 1 ∧
      (∀ r, r < 905 ∨ 908 < r → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have ht0 := (e t0).isLt
  have hπ := (e (π t0)).isLt
  obtain ⟨c₁, k₁, ex₁, hk₁, hm₁, h906, h908', h907, hreg₁, hrr₁, hrm₁, ho₁⟩ :=
    olNewB_exec (P := P) c hw h901 h902 h904 h908 h905 (by omega) (by omega)
      (by rw [hp]; omega)
  rw [hp] at h906 h908' h907
  have hJ : WalkJ (π := π) (e := e) W n bL cnt t0 (π t0) c.nmem c₁ c₁ := by
    refine ⟨ex₁.wb_right, Equiv.Perm.sameCycle_apply_right.2 (Equiv.Perm.SameCycle.refl _ _),
      h906, h908', h907, fun _ _ _ _ => rfl, rfl, rfl, rfl, fun a ha => ?_, fun y hy => ?_, ?_,
      fun y hy hl => ?_⟩
    · rw [hm₁, upd_apply]; simp only [ha t0 (Equiv.Perm.SameCycle.refl _ _), ↓reduceIte]
    · rw [hm₁, upd_apply]
      split_ifs
      · exact Or.inl rfl
      · exact Or.inr (hun y hy)
    · rw [hm₁, upd_apply]; simp
    · by_cases hy0 : y = t0
      · subst hy0; exact Or.inr rfl
      · have hne : ¬ bL + (e y : ℕ) = bL + e t0 := fun h' => hy0 (e_add_inj h')
        rw [hm₁, upd_apply] at hl
        simp only [hne, ↓reduceIte] at hl
        rw [hun y hy] at hl; omega
  have hcu := cUnl_upd (π := π) (e := e) (v := cnt) (Equiv.Perm.SameCycle.refl _ t0)
    (hun t0 (Equiv.Perm.SameCycle.refl _ _)) (by omega)
  rw [← hm₁] at hcu
  obtain ⟨c₂, k₂, ex₂, hk₂, hall, hfr, hreg₂, hrr₂, hrm₂, ho₂⟩ :=
    olWalk_exec (P := P) hJ (by rw [hreg₁ 900 (by omega) (by omega) (by omega), h900])
      (by rw [hreg₁ 901 (by omega) (by omega) (by omega), h901])
      (by rw [hreg₁ 902 (by omega) (by omega) (by omega), h902])
      (by rw [hreg₁ 905 (by omega) (by omega) (by omega), h905]) (by omega) hp hd wp wL
  have e905 : c₂.nreg 905 = cnt := by
    rw [hreg₂ 905 (by omega) (by omega) (by omega), hreg₁ 905 (by omega) (by omega) (by omega),
      h905]
  have e10 : c₂.nreg 10 = 1 := by
    rw [hreg₂ 10 (by omega) (by omega) (by omega), hreg₁ 10 (by omega) (by omega) (by omega),
      h10]
  have ex₃ := Exec.addN (P := P) ex₂.wb_right 905 905 10 (by rw [e905, e10]; omega)
  refine ⟨_, k₁ + (k₂ + 1), Exec.seq ex₁ (Exec.seq ex₂ ex₃), by omega, by omega, hall,
    hfr, ?_, fun r hr => ?_, ?_, ?_, ?_⟩
  · config_simp; rw [e905, e10]
  · config_simp
    rw [upd_other _ _ _ (show r ≠ 905 by omega), hreg₂ r (by omega) (by omega) (by omega),
      hreg₁ r (by omega) (by omega) (by omega)]
  · simp only [Config.rreg_mk]; rw [hrr₂, hrr₁]
  · simp only [Config.rmem_mk]; rw [hrm₂, hrm₁]
  · simp only [Config.output_mk]; rw [ho₂, ho₁]

lemma aUnl_relabel {t0 : T} {bL cnt : ℕ} {mem mem' : ℕ → ℕ} (hcnt : cnt ≠ n + 1)
    (hun : ∀ y, π.SameCycle t0 y → mem (bL + e y) = n + 1)
    (hall : ∀ y, π.SameCycle t0 y → mem' (bL + e y) = cnt)
    (hfr : ∀ y, ¬ π.SameCycle t0 y → mem' (bL + e y) = mem (bL + e y)) :
    aUnl e bL mem' + cUnl π e t0 bL mem = aUnl e bL mem := by
  classical
  unfold aUnl cUnl
  rw [← card_union_of_disjoint]
  · congr 1
    ext y
    simp only [mem_union, mem_filter, mem_univ, true_and]
    by_cases hy : π.SameCycle t0 y
    · simp [hy, hall y hy, hun y hy, hcnt]
    · simp [hy, hfr y hy]
  · rw [disjoint_left]
    intro y h1 h2
    simp only [mem_filter, mem_univ, true_and] at h1 h2
    rw [hall y h2.1] at h1; exact hcnt h1

/-- The state of the orbit labelling after the elements `< c.nreg 904`, from `c₀`. -/
structure OrbI (W n bL : ℕ) (c₀ c : Config) : Prop where
  wb : WordsBounded W c
  le : c.nreg 904 ≤ n
  cnt : c.nreg 905 ≤ c.nreg 904
  r903 : c.nreg 903 = n + 1
  reg : ∀ r, r < 903 ∨ 908 < r → c.nreg r = c₀.nreg r
  rreg : c.rreg = c₀.rreg
  rmem : c.rmem = c₀.rmem
  out : c.output = c₀.output
  fr : ∀ a, (a < bL ∨ bL + n ≤ a) → c.nmem a = c₀.nmem a
  lab : ∀ y, (∃ y', (e y' : ℕ) < c.nreg 904 ∧ π.SameCycle y' y) →
    c.nmem (bL + e y) < c.nreg 905
  unl : ∀ y, (¬ ∃ y', (e y' : ℕ) < c.nreg 904 ∧ π.SameCycle y' y) → c.nmem (bL + e y) = n + 1
  eq : ∀ y y', c.nmem (bL + e y) < c.nreg 905 → c.nmem (bL + e y') < c.nreg 905 →
    (c.nmem (bL + e y) = c.nmem (bL + e y') ↔ π.SameCycle y y')
  surj : ∀ ℓ < c.nreg 905, ∃ y, c.nmem (bL + e y) = ℓ

set_option maxHeartbeats 1000000 in
/-- **One element of the scan** keeps the state of the orbit labelling, paying for the walk of a
new cycle by its unlabelled elements. -/
theorem olBody_step {bp bL : ℕ} {c₀ c : Config} (hI : OrbI (π := π) (e := e) W n bL c₀ c)
    (h900 : c₀.nreg 900 = n) (h901 : c₀.nreg 901 = bp) (h902 : c₀.nreg 902 = bL)
    (h10 : c₀.nreg 10 = 1) (hp : ∀ t, c₀.nmem (bp + e t) = e (π t))
    (hd : bp + n ≤ bL ∨ bL + n ≤ bp) (wp : bp + n ≤ W) (wL : bL + n ≤ W) (wn : n + 2 ≤ W)
    (hlt : c.nreg 904 < n) :
    ∃ c' k, Exec P W olBody c c' k ∧ OrbI (π := π) (e := e) W n bL c₀ c' ∧
      20 * (n - c'.nreg 904) + 7 * aUnl e bL c'.nmem + k + 2 ≤
        20 * (n - c.nreg 904) + 7 * aUnl e bL c.nmem := by
  set i := c.nreg 904 with hi
  set cnt := c.nreg 905 with hcnt
  set t0 := e.symm ⟨i, hlt⟩ with ht0
  have he : (e t0 : ℕ) = i := by rw [ht0, Equiv.apply_symm_apply]
  have hcn := hI.cnt
  have g900 : c.nreg 900 = n := (hI.reg 900 (by omega)).trans h900
  have g901 : c.nreg 901 = bp := (hI.reg 901 (by omega)).trans h901
  have g902 : c.nreg 902 = bL := (hI.reg 902 (by omega)).trans h902
  have g10 : c.nreg 10 = 1 := (hI.reg 10 (by omega)).trans h10
  have gp : ∀ t, c.nmem (bp + e t) = e (π t) := fun t => by
    have := (e t).isLt
    rw [hI.fr _ (by omega)]; exact hp t
  obtain ⟨c₁, k₁, ex₁, hk₁, hm₁, h908, h907, hreg₁, hrr₁, hrm₁, ho₁⟩ :=
    olBodyB_exec (P := P) c hI.wb g902 rfl (by omega)
  have r1 : ∀ r, r ≠ 907 → r ≠ 908 → c₁.nreg r = c.nreg r := hreg₁
  unfold olBody
  by_cases hx : n < c.nmem (bL + i)
  · -- a new cycle
    have hun : ∀ y, π.SameCycle t0 y → c.nmem (bL + e y) = n + 1 := by
      intro y hy
      refine hI.unl y fun ⟨y', hy', hs⟩ => ?_
      have := hI.lab t0 ⟨y', hy', hs.trans hy.symm⟩
      rw [he] at this; omega
    obtain ⟨c₂, k₂, ex₂, hk₂, hc1, hall, hfr, h905, hreg₂, hrr₂, hrm₂, ho₂⟩ :=
      olNew_exec (P := P) (π := π) (e := e) (t0 := t0) ex₁.wb_right
        (by rw [r1 900 (by omega) (by omega), g900]) (by rw [r1 901 (by omega) (by omega), g901])
        (by rw [r1 902 (by omega) (by omega), g902]) (by rw [r1 904 (by omega) (by omega), he])
        (by rw [r1 905 (by omega) (by omega)]) (by rw [h908, he])
        (by rw [r1 10 (by omega) (by omega), g10]) (by omega) (fun y hy => by rw [hm₁]; exact hun y hy)
        (fun t => by rw [hm₁]; exact gp t) hd wp wL
    rw [hm₁] at hk₂ hc1 hfr
    have e904 : c₂.nreg 904 = i := by rw [hreg₂ 904 (by omega), r1 904 (by omega) (by omega)]
    have e10 : c₂.nreg 10 = 1 := by rw [hreg₂ 10 (by omega), r1 10 (by omega) (by omega), g10]
    have ex₃ := Exec.addN (P := P) ex₂.wb_right 904 904 10 (by rw [e904, e10]; omega)
    have hoff : ∀ y, ¬ π.SameCycle t0 y → c₂.nmem (bL + e y) = c.nmem (bL + e y) :=
      fun y hy => hfr _ fun y' hy' h' => hy (by rw [e_add_inj h']; exact hy')
    have hlt' : ∀ y, ¬ π.SameCycle t0 y → c₂.nmem (bL + e y) < cnt + 1 →
        c.nmem (bL + e y) < cnt := by
      intro y hy h
      rw [hoff y hy] at h
      by_cases hl : ∃ y', (e y' : ℕ) < i ∧ π.SameCycle y' y
      · exact hI.lab y hl
      · rw [hI.unl y hl] at h; omega
    have hA := aUnl_relabel (π := π) (e := e) (mem := c.nmem) (mem' := c₂.nmem) (cnt := cnt)
      (by omega) hun hall hoff
    refine ⟨_, k₁ + (k₂ + 1 + 1), Exec.seq ex₁ (Exec.seq (Exec.ifLtN_true
      (by rw [r1 900 (by omega) (by omega), g900, h907]; exact hx) ex₂) ex₃), ⟨ex₃.wb_right,
      ?_, ?_, ?_, fun r hr => ?_, ?_, ?_, ?_, fun a ha => ?_, fun y hy => ?_, fun y hy => ?_,
      fun y y' h1 h2 => ?_, fun ℓ hℓ => ?_⟩, ?_⟩
    all_goals simp only [Config.nreg_mk, Config.nmem_mk, Config.rreg_mk, Config.rmem_mk,
      Config.output_mk, upd_same, e904, e10] at *
    all_goals try rw [upd_other _ _ _ (show (905 : ℕ) ≠ 904 by omega), h905] at *
    · omega
    · omega
    · rw [upd_other _ _ _ (show (903 : ℕ) ≠ 904 by omega), hreg₂ 903 (by omega),
        r1 903 (by omega) (by omega)]; exact hI.r903
    · rw [upd_other _ _ _ (show r ≠ 904 by omega), hreg₂ r (by omega),
        r1 r (by omega) (by omega)]; exact hI.reg r hr
    · rw [hrr₂, hrr₁, hI.rreg]
    · rw [hrm₂, hrm₁, hI.rmem]
    · rw [ho₂, ho₁, hI.out]
    · rw [hfr a fun y _ h' => by have := (e y).isLt; omega]; exact hI.fr a ha
    · by_cases hyC : π.SameCycle t0 y
      · rw [hall y hyC]; omega
      · obtain ⟨y', hy', hs⟩ := hy
        rw [hoff y hyC]
        by_cases hy'i : (e y' : ℕ) = i
        · have : y' = t0 := e.injective (Fin.ext (by rw [hy'i, he]))
          rw [this] at hs; exact absurd hs hyC
        · have := hI.lab y ⟨y', by omega, hs⟩; omega
    · have hyC : ¬ π.SameCycle t0 y := fun h => hy ⟨t0, by omega, h⟩
      rw [hoff y hyC]
      exact hI.unl y fun ⟨y', hy', hs⟩ => hy ⟨y', by omega, hs⟩
    · by_cases hyC : π.SameCycle t0 y <;> by_cases hyC' : π.SameCycle t0 y'
      · rw [hall y hyC, hall y' hyC']; exact ⟨fun _ => hyC.symm.trans hyC', fun _ => rfl⟩
      · have := hlt' y' hyC' h2
        rw [hall y hyC, hoff y' hyC']
        exact ⟨fun h => by omega, fun h => absurd (hyC.trans h) hyC'⟩
      · have := hlt' y hyC h1
        rw [hall y' hyC', hoff y hyC]
        exact ⟨fun h => by omega, fun h => absurd (hyC'.trans h.symm) hyC⟩
      · rw [hoff y hyC, hoff y' hyC']
        exact hI.eq y y' (hlt' y hyC h1) (hlt' y' hyC' h2)
    · by_cases hℓc : ℓ = cnt
      · exact ⟨t0, by rw [hall t0 (Equiv.Perm.SameCycle.refl _ _), hℓc]⟩
      · obtain ⟨y, hy⟩ := hI.surj ℓ (by omega)
        have hyC : ¬ π.SameCycle t0 y := fun h => by rw [hun y h] at hy; omega
        exact ⟨y, by rw [hoff y hyC, hy]⟩
    · omega
  · -- an element already labelled
    have hl0 : ∃ y', (e y' : ℕ) < i ∧ π.SameCycle y' t0 := by
      by_contra h
      have := hI.unl t0 h
      rw [he] at this; omega
    obtain ⟨y0, hy0, hs0⟩ := hl0
    have e904 : c₁.nreg 904 = i := r1 904 (by omega) (by omega)
    have e10 : c₁.nreg 10 = 1 := by rw [r1 10 (by omega) (by omega), g10]
    have ex₃ := Exec.addN (P := P) ex₁.wb_right 904 904 10 (by rw [e904, e10]; omega)
    refine ⟨_, k₁ + (0 + 2 + 1), Exec.seq ex₁ (Exec.seq (Exec.ifLtN_false
      (by rw [r1 900 (by omega) (by omega), g900, h907]; exact hx) (Exec.skip ex₁.wb_right))
      ex₃), ⟨ex₃.wb_right, ?_, ?_, ?_, fun r hr => ?_, ?_, ?_, ?_, fun a ha => ?_,
      fun y hy => ?_, fun y hy => ?_, fun y y' h1 h2 => ?_, fun ℓ hℓ => ?_⟩, ?_⟩
    all_goals simp only [Config.nreg_mk, Config.nmem_mk, Config.rreg_mk, Config.rmem_mk,
      Config.output_mk, upd_same, e904, e10, hm₁] at *
    all_goals try rw [upd_other _ _ _ (show (905 : ℕ) ≠ 904 by omega),
      r1 905 (by omega) (by omega)] at *
    · omega
    · omega
    · rw [upd_other _ _ _ (show (903 : ℕ) ≠ 904 by omega), r1 903 (by omega) (by omega)]
      exact hI.r903
    · rw [upd_other _ _ _ (show r ≠ 904 by omega), r1 r (by omega) (by omega)]
      exact hI.reg r hr
    · rw [hrr₁, hI.rreg]
    · rw [hrm₁, hI.rmem]
    · rw [ho₁, hI.out]
    · exact hI.fr a ha
    · obtain ⟨y', hy', hs⟩ := hy
      by_cases hy'i : (e y' : ℕ) = i
      · have : y' = t0 := e.injective (Fin.ext (by rw [hy'i, he]))
        rw [this] at hs; exact hI.lab y ⟨y0, hy0, hs0.trans hs⟩
      · exact hI.lab y ⟨y', by omega, hs⟩
    · exact hI.unl y fun ⟨y', hy', hs⟩ => hy ⟨y', by omega, hs⟩
    · exact hI.eq y y' h1 h2
    · exact hI.surj ℓ hℓ
    · omega

lemma aUnl_le (bL : ℕ) (mem : ℕ → ℕ) : aUnl e bL mem ≤ n := by
  classical
  unfold aUnl
  refine (card_filter_le _ _).trans ?_
  rw [card_univ, Fintype.card_congr e, Fintype.card_fin]

set_option maxHeartbeats 1000000 in
/-- **Orbit labelling on the machine.** From a permutation `π` of `T` given as an array under a
numbering `e : T ≃ Fin n` (at `bp + e t` the number `e (π t)`), `orbProg` writes at `bL + e t`
a label per element, equal exactly for elements of one cycle, the labels being exactly
`0, …, r905 - 1`, within `32 n + 8` steps. -/
theorem orbProg_exec {bp bL : ℕ} (c : Config) (hc : WordsBounded W c)
    (h900 : c.nreg 900 = n) (h901 : c.nreg 901 = bp) (h902 : c.nreg 902 = bL)
    (h10 : c.nreg 10 = 1) (hp : ∀ t, c.nmem (bp + e t) = e (π t))
    (hd : bp + n ≤ bL ∨ bL + n ≤ bp) (wp : bp + n ≤ W) (wL : bL + n ≤ W) (wn : n + 2 ≤ W) :
    ∃ c' k, Exec P W orbProg c c' k ∧ k ≤ 32 * n + 8 ∧
      (∀ y, c'.nmem (bL + e y) < c'.nreg 905) ∧
      (∀ y y', c'.nmem (bL + e y) = c'.nmem (bL + e y') ↔ π.SameCycle y y') ∧
      (∀ ℓ < c'.nreg 905, ∃ y, c'.nmem (bL + e y) = ℓ) ∧
      (∀ r, r < 903 ∨ 908 < r → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output ∧
      (∀ a, (a < bL ∨ bL + n ≤ a) → c'.nmem a = c.nmem a) := by
  unfold orbProg
  refine spec_seq ?_
  exec_block
  all_goals try ((try config_simp); (try simp only [h900, h10]) <;> omega)
  rename_i hw1
  -- the marks
  let J : ℕ → Config → Prop := fun i c' =>
    (∀ r, r < 904 ∨ 908 < r → c'.nreg r = upd c.nreg 903 (n + 1) r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output ∧
      (∀ a, (a < bL ∨ bL + i ≤ a) → c'.nmem a = c.nmem a) ∧ (∀ x < i, c'.nmem (bL + x) = n + 1)
  refine spec_seq ?_
  refine spec_use (forLoop_exec (P := P) (a := 904) (bR := 900) (body := olInit) J (K := 3)
    (n := n) _ hw1 (by config_simp) (by config_simp; exact h900) ?_
    (fun i c₂ hi hw₂ ha hb ⟨fr, frr, frm, fo, fm, f0⟩ => ?_)) ?_
  · refine ⟨fun r hr => ?_, rfl, rfl, rfl, fun _ _ => rfl, fun _ h => absurd h (by omega)⟩
    config_simp; simp only [upd_apply]; split_ifs <;> first | omega | rfl
  · have g902 : c₂.nreg 902 = bL := by rw [fr 902 (by omega), upd_apply]; simpa using h902
    have g903 : c₂.nreg 903 = n + 1 := by rw [fr 903 (by omega), upd_apply]; simp
    have g10 : c₂.nreg 10 = 1 := by rw [fr 10 (by omega), upd_apply]; simpa using h10
    unfold olInit
    exec_block
    all_goals try ((try config_simp); (try simp only [g902, g10, ha]) <;> omega)
    refine ⟨by omega, by config_simp; simp only [g10, ha], by config_simp; exact hb,
      fun r hr => ?_, frr, frm, fo, fun a ha' => ?_, fun x hx => ?_⟩
    · config_simp
      have h1 : r ≠ 904 := by omega
      have h2 : r ≠ 908 := by omega
      simp only [upd_other _ _ _ h1, upd_other _ _ _ h2]; exact fr r hr
    · config_simp; simp only [upd_apply, g902, ha]
      split_ifs <;> first | omega | exact fm a (by omega)
    · config_simp; simp only [upd_apply, g902, ha, g903]
      split_ifs <;> first | omega | exact f0 x (by omega)
  intro c₂ k₂ hk₂ hw₂ ⟨_, fr, frr, frm, fo, fm, f0⟩
  have g10 : c₂.nreg 10 = 1 := by rw [fr 10 (by omega), upd_apply]; simpa using h10
  refine spec_seq ?_
  exec_block
  all_goals try omega
  rename_i hw3
  -- the scan
  set c₃ := ({ c₂ with nreg := upd (upd c₂.nreg 904 0) 905 0 } : Config) with hc₃
  have hI : OrbI (π := π) (e := e) W n bL c c₃ := by
    refine ⟨hw3, by rw [hc₃]; config_simp; omega, by rw [hc₃]; config_simp; omega,
      by rw [hc₃]; config_simp; rw [fr 903 (by omega)]; simp, fun r hr => ?_, frr, frm, fo,
      fun a ha => fm a (by omega), fun y ⟨y', hy', _⟩ => ?_, fun y _ => ?_,
      fun y y' h1 _ => ?_, fun ℓ hℓ => ?_⟩
    · rw [hc₃]; config_simp
      rw [upd_other _ _ _ (show r ≠ 905 by omega), upd_other _ _ _ (show r ≠ 904 by omega),
        fr r (by omega), upd_other _ _ _ (show r ≠ 903 by omega)]
    · rw [hc₃] at hy'; simp at hy'
    · exact f0 _ (e y).isLt
    · rw [hc₃] at h1; simp at h1
    · rw [hc₃] at hℓ; simp at hℓ
  have hc₃' : c₃.nreg 904 = 0 := by rw [hc₃]; config_simp
  have hA := aUnl_le (e := e) bL c₃.nmem
  refine spec_while (fun c' => OrbI (π := π) (e := e) W n bL c c')
    (fun c' => 20 * (n - c'.nreg 904) + 7 * aUnl e bL c'.nmem) (fun c' h => h.wb) ?_ hI ?_
  · intro c' h hlt
    have g900 : c'.nreg 900 = n := (h.reg 900 (by omega)).trans h900
    rw [g900] at hlt
    exact olBody_step h h900 h901 h902 h10 hp hd wp wL wn hlt
  · intro c' k h hn hk
    have g900 : c'.nreg 900 = n := (h.reg 900 (by omega)).trans h900
    rw [g900] at hn
    have hall : ∀ y, c'.nmem (bL + e y) < c'.nreg 905 := fun y =>
      h.lab y ⟨y, by have := (e y).isLt; omega, Equiv.Perm.SameCycle.refl _ _⟩
    refine ⟨by rw [hc₃'] at hk; omega, hall, fun y y' => h.eq y y' (hall y) (hall y'),
      h.surj, h.reg, h.rreg, h.rmem, h.out, h.fr⟩

end Orb

/-! ### Numberings from labels and ranks -/

/-- **Labels as a numbering**: labels `< n` of the elements of `T`, equal exactly over the fibres
of a surjection `q : T → Q` and taking every value `< n`, number `Q`. -/
theorem exists_equiv_of_lab {T Q : Type*} {q : T → Q} (hq : Function.Surjective q)
    {lab : T → ℕ} {n : ℕ} (hlt : ∀ t, lab t < n) (heq : ∀ t t', lab t = lab t' ↔ q t = q t')
    (hs : ∀ ℓ < n, ∃ t, lab t = ℓ) : ∃ E : Q ≃ Fin n, ∀ t, (E (q t) : ℕ) = lab t := by
  let f : Q → Fin n := fun x => ⟨lab (hq x).choose, hlt _⟩
  have hf : ∀ t, (f (q t) : ℕ) = lab t := fun t => (heq _ _).2 (hq (q t)).choose_spec
  have hinj : Function.Injective f := by
    intro x y hxy
    have := (heq _ _).1 (congrArg Fin.val hxy)
    rwa [(hq x).choose_spec, (hq y).choose_spec] at this
  have hsurj : Function.Surjective f := by
    intro ℓ
    obtain ⟨t, ht⟩ := hs ℓ ℓ.isLt
    exact ⟨q t, Fin.ext (by rw [hf, ht])⟩
  exact ⟨Equiv.ofBijective f ⟨hinj, hsurj⟩, fun t => hf t⟩

/-- The number of `h' < h` with `q h'`: the rank of `h` among them. -/
def prk (q : ℕ → Prop) [DecidablePred q] (h : ℕ) : ℕ := ((range h).filter q).card

section Rank

variable {q : ℕ → Prop} [DecidablePred q]

lemma prk_succ (h : ℕ) : prk q (h + 1) = prk q h + if q h then 1 else 0 := by
  unfold prk; rw [range_add_one, filter_insert]
  split_ifs with hq
  · rw [card_insert_of_notMem (fun h' => by simp at h')]
  · rfl

lemma prk_mono {h h' : ℕ} (hh : h ≤ h') : prk q h ≤ prk q h' :=
  card_le_card (filter_subset_filter _ (range_subset_range.2 hh))

lemma prk_lt {h h' : ℕ} (hq : q h) (hh : h < h') : prk q h < prk q h' := by
  have := prk_mono (q := q) (show h + 1 ≤ h' by omega)
  rw [prk_succ] at this; simp only [hq, ↓reduceIte] at this; omega

lemma prk_le (h : ℕ) : prk q h ≤ h := (card_filter_le _ _).trans (card_range h).le

lemma prk_inj {h h' : ℕ} (hq : q h) (hq' : q h') (e : prk q h = prk q h') : h = h' := by
  rcases lt_trichotomy h h' with hl | rfl | hl
  · exact absurd e (prk_lt hq hl).ne
  · rfl
  · exact absurd e (prk_lt hq' hl).ne'

lemma prk_surj {k ℓ : ℕ} (hℓ : ℓ < prk q k) : ∃ h < k, q h ∧ prk q h = ℓ := by
  induction k with
  | zero => simp [prk] at hℓ
  | succ k ih =>
    rw [prk_succ] at hℓ
    by_cases hl : ℓ < prk q k
    · obtain ⟨h, hh, hq, e⟩ := ih hl
      exact ⟨h, by omega, hq, e⟩
    · by_cases hq : q k
      · simp only [hq, ↓reduceIte] at hℓ
        exact ⟨k, by omega, hq, by omega⟩
      · simp only [hq, ↓reduceIte] at hℓ; omega

/-- **The numbering by ranks**: an enumeration `δ` of `S` by `0, …, k - 1` and a part `S'` of
`S` read by a predicate `q` number `S'` by the ranks among the `h` with `q h`. -/
theorem exists_rank_equiv {D : Type*} {S S' : Finset D} {k : ℕ} {δ : ℕ → D}
    (he : IsEnum k δ S) (hS : S' ⊆ S) (hq : ∀ h < k, (q h ↔ δ h ∈ S')) :
    ∃ c : {x // x ∈ S'} ≃ Fin (prk q k), ∀ h < k, ∀ (hm : δ h ∈ S'), (c ⟨δ h, hm⟩ : ℕ) = prk q h := by
  have hc : ∀ d : {x // x ∈ S'}, ∃ h < k, δ h = d.1 := fun d => he.surj _ (hS d.2)
  let ch : {x // x ∈ S'} → ℕ := fun d => (hc d).choose
  have hch : ∀ d, ch d < k ∧ δ (ch d) = d.1 := fun d => (hc d).choose_spec
  have hqch : ∀ d, q (ch d) := fun d => (hq _ (hch d).1).2 (by rw [(hch d).2]; exact d.2)
  let f : {x // x ∈ S'} → Fin (prk q k) := fun d => ⟨prk q (ch d), prk_lt (hqch d) (hch d).1⟩
  have hinj : Function.Injective f := by
    intro d d' e
    have := prk_inj (hqch d) (hqch d') (congrArg Fin.val e)
    exact Subtype.ext (by rw [← (hch d).2, ← (hch d').2, this])
  have hsurj : Function.Surjective f := by
    intro ℓ
    obtain ⟨h, hh, hqh, e⟩ := prk_surj ℓ.isLt
    have hm := (hq h hh).1 hqh
    refine ⟨⟨δ h, hm⟩, Fin.ext ?_⟩
    have := he.inj _ (hch ⟨δ h, hm⟩).1 h hh (hch ⟨δ h, hm⟩).2
    change prk q (ch ⟨δ h, hm⟩) = ℓ
    rw [this, e]
  refine ⟨Equiv.ofBijective f ⟨hinj, hsurj⟩, fun h hh hm => ?_⟩
  change prk q (ch ⟨δ h, hm⟩) = prk q h
  rw [he.inj _ (hch ⟨δ h, hm⟩).1 h hh (hch ⟨δ h, hm⟩).2]

end Rank

/-! ### The encoding program

Registers: `r910 = k` (the half-edges of the piece), `r911 = m` (its darts), `r912 = bα` (the
reversal), `r913 = bσ` (the rotation of the piece), `r914 = bF` (the flags of the component),
`r915 = B₀` (the output), `r916 = X` (the scratch: the ranks at `X + h`, the half-edges of the
component by rank at `X + k + i`, the rotation of the component at `X + 2 k + i`), `r10 = 1`. -/

/-- The dart of the piece of the half-edge `h`, read from the memory. -/
def cmU (m bα : ℕ) (mem : ℕ → ℕ) (h : ℕ) : ℕ := if h < m then h else mem (bα + h)

/-- One half-edge `h = r917` of the compaction: its rank `r918` at `X + h`, and, if its dart is
flagged, `h` at `X + k + r918` (`r923 = X + k`) and the rank counted. -/
def cmBody : Stmt :=
  .seq (.ifLtN 917 911 (.instr (.copyN 919 917)) (block [.addN 920 912 917, .loadN 919 920])) <|
  .seq (block [.addN 920 914 919, .loadN 921 920, .addN 920 916 917, .storeN 920 918]) <|
  .seq (.ifLtN 921 10 .skip (block [.addN 920 923 918, .storeN 920 917, .addN 918 918 10]))
    (.instr (.addN 917 917 10))

set_option maxHeartbeats 1000000 in
/-- One step of the compaction. -/
theorem cmBody_exec {k m bα bF X h cnt : ℕ} (c₁ : Config) (hw : WordsBounded W c₁)
    (h910 : c₁.nreg 910 = k) (h911 : c₁.nreg 911 = m) (h912 : c₁.nreg 912 = bα)
    (h914 : c₁.nreg 914 = bF) (h916 : c₁.nreg 916 = X) (h923 : c₁.nreg 923 = X + k)
    (h10 : c₁.nreg 10 = 1) (h917 : c₁.nreg 917 = h) (h918 : c₁.nreg 918 = cnt) (hh : h < k)
    (hc : cnt ≤ h) (wα : bα + k ≤ W) (wF : bF + cmU m bα c₁.nmem h ≤ W) (wX : X + 2 * k ≤ W) :
    ∃ c' s, Exec P W cmBody c₁ c' s ∧ s ≤ 14 ∧ c'.nreg 917 = h + 1 ∧
      c'.nreg 918 = cnt + (if c₁.nmem (bF + cmU m bα c₁.nmem h) = 0 then 0 else 1) ∧
      c'.nmem = (if c₁.nmem (bF + cmU m bα c₁.nmem h) = 0 then upd c₁.nmem (X + h) cnt
        else upd (upd c₁.nmem (X + h) cnt) (X + k + cnt) h) ∧
      (∀ r, r < 917 ∨ 921 < r → c'.nreg r = c₁.nreg r) ∧
      c'.rreg = c₁.rreg ∧ c'.rmem = c₁.rmem ∧ c'.output = c₁.output := by
  unfold cmBody
  -- the dart `u`
  have hU : ∃ c₂ s₂, Exec P W (.ifLtN 917 911 (.instr (.copyN 919 917))
      (block [.addN 920 912 917, .loadN 919 920])) c₁ c₂ s₂ ∧ s₂ ≤ 4 ∧
      c₂.nreg 919 = cmU m bα c₁.nmem h ∧ c₂.nmem = c₁.nmem ∧
      (∀ r, r ≠ 919 → r ≠ 920 → c₂.nreg r = c₁.nreg r) ∧
      c₂.rreg = c₁.rreg ∧ c₂.rmem = c₁.rmem ∧ c₂.output = c₁.output := by
    by_cases hm : h < m
    · refine spec_ifLtN_true (by rw [h917, h911]; exact hm) ?_
      refine spec_instr (Exec.copyN hw 919 917) fun _ => ?_
      config_simp
      simp only [cmU, hm, h917, ↓reduceIte]
      and_intros
      all_goals first | omega | rfl | trivial | (intro r h1 h2; simp [h1])
    · refine spec_ifLtN_false (by rw [h917, h911]; exact hm) ?_
      exec_block
      all_goals try ((try config_simp); (try simp only [h912, h917]) <;> omega)
      config_simp
      simp only [h912, h917, cmU, hm, ↓reduceIte]
      and_intros
      all_goals first | omega | rfl | trivial | (intro r h1 h2; simp [h1, h2])
  obtain ⟨c₂, s₂, ex₂, hs₂, h919, hm₂, hr₂, hrr₂, hrm₂, ho₂⟩ := hU
  have g : ∀ r, r ≠ 919 → r ≠ 920 → c₂.nreg r = c₁.nreg r := hr₂
  have hw₂ := ex₂.wb_right
  refine spec_seq ⟨c₂, s₂, ex₂, ?_⟩
  have e914 : c₂.nreg 914 = bF := by rw [g 914 (by omega) (by omega), h914]
  have e916 : c₂.nreg 916 = X := by rw [g 916 (by omega) (by omega), h916]
  have e917 : c₂.nreg 917 = h := by rw [g 917 (by omega) (by omega), h917]
  have e918 : c₂.nreg 918 = cnt := by rw [g 918 (by omega) (by omega), h918]
  have e923 : c₂.nreg 923 = X + k := by rw [g 923 (by omega) (by omega), h923]
  have e10 : c₂.nreg 10 = 1 := by rw [g 10 (by omega) (by omega), h10]
  have gf : ∀ r, r < 917 ∨ 921 < r → c₂.nreg r = c₁.nreg r := fun r hr => g r (by omega) (by omega)
  refine spec_seq ?_
  exec_block
  all_goals try ((try config_simp); (try simp only [e914, e916, e917, h919]) <;> omega)
  refine spec_seq ?_
  by_cases hf : c₁.nmem (bF + cmU m bα c₁.nmem h) = 0
  · refine spec_ifLtN_true (by config_simp; simp only [e914, h919, hm₂, hf, e10]; omega) ?_
    refine spec_skip ‹_› ?_
    refine spec_instr (Exec.addN ‹_› 917 917 10 (by config_simp; simp only [e917, e10]; omega))
      fun _ => ?_
    config_simp
    simp only [e914, e916, e917, e918, e10, h919, hm₂, hf, ↓reduceIte]
    and_intros
    all_goals try omega
    all_goals try rfl
    all_goals try trivial
    all_goals try (intro r hr; simp only [upd_apply]; split_ifs <;> first | omega | exact gf r hr)
  · refine spec_ifLtN_false (by config_simp; simp only [e914, h919, hm₂, e10]; omega) ?_
    exec_block
    all_goals try ((try config_simp); (try simp only [e914, e916, e917, e918, e923, h919, e10])
      <;> omega)
    refine spec_instr (Exec.addN ‹_› 917 917 10 (by config_simp; simp only [e917, e10]; omega))
      fun _ => ?_
    config_simp
    simp only [e914, e916, e917, e918, e923, e10, h919, hm₂, hf, ↓reduceIte]
    and_intros
    all_goals try omega
    all_goals try rfl
    all_goals try trivial
    all_goals try (intro r hr; simp only [upd_apply]; split_ifs <;> first | omega | exact gf r hr)

set_option maxHeartbeats 1000000 in
/-- **The compaction**: the ranks of the half-edges `h < k` among those whose dart is flagged
(`q h`), at `X + h`; the flagged ones by rank at `X + k + i`; their number in `r918`. -/
theorem cmLoop_exec {k m bα bF X : ℕ} (c₁ : Config) (hw : WordsBounded W c₁)
    (h910 : c₁.nreg 910 = k) (h911 : c₁.nreg 911 = m) (h912 : c₁.nreg 912 = bα)
    (h914 : c₁.nreg 914 = bF) (h916 : c₁.nreg 916 = X) (h923 : c₁.nreg 923 = X + k)
    (h10 : c₁.nreg 10 = 1) (h917 : c₁.nreg 917 = 0) (h918 : c₁.nreg 918 = 0)
    (hu : ∀ h < k, cmU m bα c₁.nmem h < m) (wα : bα + k ≤ X) (wF : bF + m ≤ X)
    (wX : X + 2 * k ≤ W) :
    ∃ c' t, Exec P W (.whileLtN 917 910 cmBody) c₁ c' t ∧ t ≤ 16 * k + 2 ∧
      c'.nreg 918 = prk (fun h => c₁.nmem (bF + cmU m bα c₁.nmem h) ≠ 0) k ∧
      (∀ h < k, c'.nmem (X + h) = prk (fun h => c₁.nmem (bF + cmU m bα c₁.nmem h) ≠ 0) h) ∧
      (∀ h < k, c₁.nmem (bF + cmU m bα c₁.nmem h) ≠ 0 →
        c'.nmem (X + k + prk (fun h => c₁.nmem (bF + cmU m bα c₁.nmem h) ≠ 0) h) = h) ∧
      (∀ a, (a < X ∨ X + 2 * k ≤ a) → c'.nmem a = c₁.nmem a) ∧
      (∀ r, r < 917 ∨ 921 < r → c'.nreg r = c₁.nreg r) ∧
      c'.rreg = c₁.rreg ∧ c'.rmem = c₁.rmem ∧ c'.output = c₁.output := by
  set q : ℕ → Prop := fun h => c₁.nmem (bF + cmU m bα c₁.nmem h) ≠ 0 with hq
  let J : ℕ → Config → Prop := fun h c' =>
    (∀ r, r < 917 ∨ 921 < r → c'.nreg r = c₁.nreg r) ∧ c'.rreg = c₁.rreg ∧
      c'.rmem = c₁.rmem ∧ c'.output = c₁.output ∧ c'.nreg 918 = prk q h ∧
      (∀ a, (a < X ∨ X + 2 * k ≤ a) → c'.nmem a = c₁.nmem a) ∧
      (∀ h' < h, c'.nmem (X + h') = prk q h') ∧ (∀ h' < h, q h' → c'.nmem (X + k + prk q h') = h')
  refine spec_use (forLoop_exec (P := P) (a := 917) (bR := 910) (body := cmBody) J (K := 14)
    (n := k) _ hw h917 h910 ?_ (fun h c₂ hh hw₂ ha hb ⟨fr, frr, frm, fo, f918, fm, fI, fP⟩ => ?_))
    ?_
  · exact ⟨fun _ _ => rfl, rfl, rfl, rfl, by rw [h918]; rfl, fun _ _ => rfl,
      fun _ h => absurd h (by omega), fun _ h => absurd h (by omega)⟩
  · have hU : cmU m bα c₂.nmem h = cmU m bα c₁.nmem h := by
      unfold cmU; split_ifs
      · rfl
      · exact fm _ (by omega)
    have hUm := hu h hh
    have hF : c₂.nmem (bF + cmU m bα c₂.nmem h) = c₁.nmem (bF + cmU m bα c₁.nmem h) := by
      rw [hU]; exact fm _ (by omega)
    have hrk := prk_le (q := q) h
    obtain ⟨c', s, ex, hs, h917', h918', hm', hreg, hrr, hrm, ho⟩ :=
      cmBody_exec (P := P) c₂ hw₂ (by rw [fr 910 (by omega), h910])
        (by rw [fr 911 (by omega), h911]) (by rw [fr 912 (by omega), h912])
        (by rw [fr 914 (by omega), h914]) (by rw [fr 916 (by omega), h916])
        (by rw [fr 923 (by omega), h923]) (by rw [fr 10 (by omega), h10]) ha f918 hh
        (by omega) (by omega) (by rw [hU]; omega) wX
    rw [hF] at h918' hm'
    refine ⟨c', s, ex, hs, h917', by rw [hreg 910 (by omega)]; exact hb,
      fun r hr => by rw [hreg r hr, fr r hr], hrr.trans frr, hrm.trans frm, ho.trans fo, ?_,
      fun a ha' => ?_, fun h' hh' => ?_, fun h' hh' hq' => ?_⟩
    · rw [h918', prk_succ]
      by_cases hf : c₁.nmem (bF + cmU m bα c₁.nmem h) = 0
      · simp [hq, hf]
      · simp [hq, hf]
    · rw [hm']
      split_ifs
      · rw [upd_apply, ite_eq_right (by omega)]; exact fm a ha'
      · rw [upd_apply, upd_apply, ite_eq_right (by omega), ite_eq_right (by omega)]; exact fm a ha'
    · rw [hm']
      by_cases e : h' = h
      · subst e
        split_ifs
        · rw [upd_apply]; simp
        · rw [upd_apply, ite_eq_right (by omega), upd_apply]; simp
      · have := fI h' (by omega)
        split_ifs
        · rw [upd_apply, ite_eq_right (by omega)]; exact this
        · rw [upd_apply, ite_eq_right (by omega), upd_apply, ite_eq_right (by omega)]; exact this
    · rw [hm']
      by_cases e : h' = h
      · subst e
        have hf : c₁.nmem (bF + cmU m bα c₁.nmem h') ≠ 0 := hq'
        simp only [hf, ↓reduceIte]
        rw [upd_apply]; simp
      · have hlt := prk_lt (q := q) hq' (show h' < h by omega)
        have := fP h' (by omega) hq'
        split_ifs
        · rw [upd_apply, ite_eq_right (by omega)]; exact this
        · rw [upd_apply, ite_eq_right (by omega), upd_apply, ite_eq_right (by omega)]; exact this
  · intro c' t ht _ ⟨_, fr, frr, frm, fo, f918, fm, fI, fP⟩
    exact ⟨by omega, f918, fI, fP, fm, fr, frr, frm, fo⟩

/-- One dart `i = r917` of the component (the half-edge `p` at `r923 + i`): its reversal, its
image under the face permutation and under the rotation, numbered by the ranks at `r916`,
written at `r915 + i`, `r924 + i`, `r929 + i`, and its flag (`p < m`) at `r928 + i`. -/
def e3Body : Stmt :=
  .seq (block [.addN 920 923 917, .loadN 930 920, .addN 920 912 930, .loadN 931 920,
    .addN 920 916 931, .loadN 932 920, .addN 920 913 931, .loadN 935 920,
    .addN 920 916 935, .loadN 935 920, .addN 920 913 930, .loadN 936 920,
    .addN 920 916 936, .loadN 936 920,
    .addN 920 915 917, .storeN 920 932, .addN 920 924 917, .storeN 920 935,
    .addN 920 929 917, .storeN 920 936]) <|
  .seq (.ifLtN 930 911 (.instr (.constN 937 1)) (.instr (.constN 937 0)))
    (block [.addN 920 928 917, .storeN 920 937, .addN 917 917 10])

set_option maxHeartbeats 2000000 in
/-- One step of the arrays of the component. -/
theorem e3Body_exec {m bα bσ bI bP bA bΦ bS bFL i p a v1 s v2 t v3 : ℕ} (c₁ : Config)
    (hw : WordsBounded W c₁) (h911 : c₁.nreg 911 = m) (h912 : c₁.nreg 912 = bα)
    (h913 : c₁.nreg 913 = bσ) (h916 : c₁.nreg 916 = bI) (h923 : c₁.nreg 923 = bP)
    (h915 : c₁.nreg 915 = bA) (h924 : c₁.nreg 924 = bΦ) (h929 : c₁.nreg 929 = bS)
    (h928 : c₁.nreg 928 = bFL) (h10 : c₁.nreg 10 = 1) (h917 : c₁.nreg 917 = i)
    (hp : c₁.nmem (bP + i) = p) (ha : c₁.nmem (bα + p) = a) (hv1 : c₁.nmem (bI + a) = v1)
    (hs : c₁.nmem (bσ + a) = s) (hv2 : c₁.nmem (bI + s) = v2) (ht : c₁.nmem (bσ + p) = t)
    (hv3 : c₁.nmem (bI + t) = v3)
    (w1 : bP + i ≤ W) (w2 : bα + p ≤ W) (w3 : bI + a ≤ W) (w4 : bσ + a ≤ W) (w5 : bI + s ≤ W)
    (w6 : bσ + p ≤ W) (w7 : bI + t ≤ W) (w8 : bA + i ≤ W) (w9 : bΦ + i ≤ W) (w10 : bS + i ≤ W)
    (w11 : bFL + i ≤ W) (w12 : i + 1 ≤ W) :
    ∃ c' k, Exec P W e3Body c₁ c' k ∧ k ≤ 27 ∧ c'.nreg 917 = i + 1 ∧
      c'.nmem = upd (upd (upd (upd c₁.nmem (bA + i) v1) (bΦ + i) v2) (bS + i) v3) (bFL + i)
        (if p < m then 1 else 0) ∧
      (∀ r, r < 917 ∨ (917 < r ∧ r < 920) ∨ (920 < r ∧ r < 930) ∨ 937 < r →
        c'.nreg r = c₁.nreg r) ∧
      c'.rreg = c₁.rreg ∧ c'.rmem = c₁.rmem ∧ c'.output = c₁.output := by
  unfold e3Body
  refine spec_seq ?_
  exec_block
  all_goals try ((try config_simp); (try simp only [h911, h912, h913, h916, h923, h915, h924,
    h929, h917, hp, ha, hv1, hs, hv2, ht, hv3]) <;> omega)
  refine spec_seq ?_
  by_cases hm : p < m
  · refine spec_ifLtN_true (by config_simp; simp only [h911, h923, h917, hp]; omega) ?_
    refine spec_instr (Exec.constN ‹_› 937 1 (by omega)) fun _ => ?_
    exec_block
    all_goals try ((try config_simp); (try simp only [h928, h917, h10]) <;> omega)
    config_simp
    simp only [h911, h912, h913, h916, h923, h915, h924, h929, h928, h917, h10, hp, ha, hv1, hs,
      hv2, ht, hv3, hm, ↓reduceIte]
    and_intros
    all_goals try omega
    all_goals try rfl
    all_goals try trivial
    all_goals try (intro r hr; simp only [upd_apply]; split_ifs <;> first | omega | rfl)
  · refine spec_ifLtN_false (by config_simp; simp only [h911, h923, h917, hp]; omega) ?_
    refine spec_instr (Exec.constN ‹_› 937 0 (by omega)) fun _ => ?_
    exec_block
    all_goals try ((try config_simp); (try simp only [h928, h917, h10]) <;> omega)
    config_simp
    simp only [h911, h912, h913, h916, h923, h915, h924, h929, h928, h917, h10, hp, ha, hv1, hs,
      hv2, ht, hv3, hm, ↓reduceIte]
    and_intros
    all_goals try omega
    all_goals try rfl
    all_goals try trivial
    all_goals try (intro r hr; simp only [upd_apply]; split_ifs <;> first | omega | rfl)

/-- The part of the memory `e3Body` leaves alone. -/
def E3Fr (m' k B₀ X a : ℕ) : Prop :=
  a < B₀ ∨ (B₀ + 2 * m' ≤ a ∧ a < B₀ + 5 * m') ∨ (B₀ + 6 * m' ≤ a ∧ a < X + 2 * k) ∨
    X + 2 * k + m' ≤ a

set_option maxHeartbeats 2000000 in
/-- **The arrays of the component**: for each rank `i < m'` (the half-edge `pos i`), the ranks
of its reversal, of its image under the face permutation `σ ∘ α` and under the rotation, and its
flag. -/
theorem e3Loop_exec {m k m' bα bσ B₀ X : ℕ} {pos α σ Ib : ℕ → ℕ} (c₁ : Config)
    (hw : WordsBounded W c₁) (h911 : c₁.nreg 911 = m) (h912 : c₁.nreg 912 = bα)
    (h913 : c₁.nreg 913 = bσ) (h916 : c₁.nreg 916 = X) (h923 : c₁.nreg 923 = X + k)
    (h915 : c₁.nreg 915 = B₀) (h924 : c₁.nreg 924 = B₀ + m') (h929 : c₁.nreg 929 = X + 2 * k)
    (h928 : c₁.nreg 928 = B₀ + 5 * m') (h918 : c₁.nreg 918 = m') (h917 : c₁.nreg 917 = 0)
    (h10 : c₁.nreg 10 = 1)
    (hpos : ∀ i < m', c₁.nmem (X + k + i) = pos i) (hα : ∀ h < k, c₁.nmem (bα + h) = α h)
    (hσ : ∀ h < k, c₁.nmem (bσ + h) = σ h) (hI : ∀ h < k, c₁.nmem (X + h) = Ib h)
    (hposk : ∀ i < m', pos i < k) (hαk : ∀ h < k, α h < k) (hσk : ∀ h < k, σ h < k)
    (hmk : m' ≤ k) (lα : bα + k ≤ B₀) (lσ : bσ + k ≤ B₀) (lB : B₀ + 6 * m' ≤ X)
    (lW : X + 3 * k ≤ W) :
    ∃ c' t, Exec P W (.whileLtN 917 918 e3Body) c₁ c' t ∧ t ≤ 29 * m' + 2 ∧
      (∀ i < m', c'.nmem (B₀ + i) = Ib (α (pos i))) ∧
      (∀ i < m', c'.nmem (B₀ + m' + i) = Ib (σ (α (pos i)))) ∧
      (∀ i < m', c'.nmem (X + 2 * k + i) = Ib (σ (pos i))) ∧
      (∀ i < m', c'.nmem (B₀ + 5 * m' + i) = if pos i < m then 1 else 0) ∧
      (∀ a, E3Fr m' k B₀ X a → c'.nmem a = c₁.nmem a) ∧
      (∀ r, r < 917 ∨ (917 < r ∧ r < 920) ∨ (920 < r ∧ r < 930) ∨ 937 < r →
        c'.nreg r = c₁.nreg r) ∧
      c'.rreg = c₁.rreg ∧ c'.rmem = c₁.rmem ∧ c'.output = c₁.output := by
  let J : ℕ → Config → Prop := fun i c' =>
    (∀ r, r < 917 ∨ (917 < r ∧ r < 920) ∨ (920 < r ∧ r < 930) ∨ 937 < r →
      c'.nreg r = c₁.nreg r) ∧
      c'.rreg = c₁.rreg ∧ c'.rmem = c₁.rmem ∧ c'.output = c₁.output ∧
      (∀ a, E3Fr m' k B₀ X a → c'.nmem a = c₁.nmem a) ∧
      (∀ i' < i, c'.nmem (B₀ + i') = Ib (α (pos i'))) ∧
      (∀ i' < i, c'.nmem (B₀ + m' + i') = Ib (σ (α (pos i')))) ∧
      (∀ i' < i, c'.nmem (X + 2 * k + i') = Ib (σ (pos i'))) ∧
      (∀ i' < i, c'.nmem (B₀ + 5 * m' + i') = if pos i' < m then 1 else 0)
  refine spec_use (forLoop_exec (P := P) (a := 917) (bR := 918) (body := e3Body) J (K := 27)
    (n := m') _ hw h917 h918 ?_
    (fun i c₂ hi hw₂ ha hb ⟨fr, frr, frm, fo, fm, f1, f2, f3, f4⟩ => ?_)) ?_
  · exact ⟨fun _ _ => rfl, rfl, rfl, rfl, fun _ _ => rfl, fun _ h => absurd h (by omega),
      fun _ h => absurd h (by omega), fun _ h => absurd h (by omega),
      fun _ h => absurd h (by omega)⟩
  · have hp := hposk i hi
    have hak := hαk _ hp
    have hs := hσk _ hak
    have ht := hσk _ hp
    have r1 : c₂.nmem (X + k + i) = pos i := by
      rw [fm _ (by unfold E3Fr; omega)]; exact hpos i hi
    have r2 : c₂.nmem (bα + pos i) = α (pos i) := by
      rw [fm _ (by unfold E3Fr; omega)]; exact hα _ hp
    have r3 : c₂.nmem (X + α (pos i)) = Ib (α (pos i)) := by
      rw [fm _ (by unfold E3Fr; omega)]; exact hI _ hak
    have r4 : c₂.nmem (bσ + α (pos i)) = σ (α (pos i)) := by
      rw [fm _ (by unfold E3Fr; omega)]; exact hσ _ hak
    have r5 : c₂.nmem (X + σ (α (pos i))) = Ib (σ (α (pos i))) := by
      rw [fm _ (by unfold E3Fr; omega)]; exact hI _ hs
    have r6 : c₂.nmem (bσ + pos i) = σ (pos i) := by
      rw [fm _ (by unfold E3Fr; omega)]; exact hσ _ hp
    have r7 : c₂.nmem (X + σ (pos i)) = Ib (σ (pos i)) := by
      rw [fm _ (by unfold E3Fr; omega)]; exact hI _ ht
    obtain ⟨c', s, ex, hs', h917', hm', hreg, hrr, hrm, ho⟩ :=
      e3Body_exec (P := P) c₂ hw₂ (by rw [fr 911 (by omega), h911])
        (by rw [fr 912 (by omega), h912]) (by rw [fr 913 (by omega), h913])
        (by rw [fr 916 (by omega), h916]) (by rw [fr 923 (by omega), h923])
        (by rw [fr 915 (by omega), h915]) (by rw [fr 924 (by omega), h924])
        (by rw [fr 929 (by omega), h929]) (by rw [fr 928 (by omega), h928])
        (by rw [fr 10 (by omega), h10]) ha r1 r2 r3 r4 r5 r6 r7 (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega)
    refine ⟨c', s, ex, hs', h917', by rw [hreg 918 (by omega)]; exact hb,
      fun r hr => by rw [hreg r (by omega), fr r hr], hrr.trans frr, hrm.trans frm, ho.trans fo,
      fun a ha' => ?_, fun i' hi' => ?_, fun i' hi' => ?_, fun i' hi' => ?_, fun i' hi' => ?_⟩
    · unfold E3Fr at ha'
      rw [hm']; simp only [upd_apply]
      split_ifs <;> first | omega | exact fm a ha'
    · rw [hm']
      by_cases e : i' = i
      · subst e
        rw [upd_other _ _ _ (by omega), upd_other _ _ _ (by omega), upd_other _ _ _ (by omega),
          upd_same]
      · simp only [upd_apply]
        split_ifs <;> first | omega | exact f1 i' (by omega)
    · rw [hm']
      by_cases e : i' = i
      · subst e
        rw [upd_other _ _ _ (by omega), upd_other _ _ _ (by omega), upd_same]
      · simp only [upd_apply]
        split_ifs <;> first | omega | exact f2 i' (by omega)
    · rw [hm']
      by_cases e : i' = i
      · subst e
        rw [upd_other _ _ _ (by omega), upd_same]
      · simp only [upd_apply]
        split_ifs <;> first | omega | exact f3 i' (by omega)
    · rw [hm']
      by_cases e : i' = i
      · subst e
        rw [upd_same]
      · rw [upd_other _ _ _ (by omega), upd_other _ _ _ (by omega), upd_other _ _ _ (by omega),
          upd_other _ _ _ (by omega)]
        exact f4 i' (by omega)
  · intro c' t ht _ ⟨_, fr, frr, frm, fo, fm, f1, f2, f3, f4⟩
    exact ⟨by omega, f1, f2, f3, f4, fm, fr, frr, frm, fo⟩

/-- The inverse of the face permutation: `i` at `r925 + Φ[i]` (`Φ` at `r924`). -/
def e4Body : Stmt :=
  block [.addN 920 924 917, .loadN 932 920, .addN 920 925 932, .storeN 920 917, .addN 917 917 10]

set_option maxHeartbeats 1000000 in
/-- **The inverse of a permutation array** `Φ` of `0, …, m' - 1` at `B₀ + m'`, written at
`B₀ + 2 m'`. -/
theorem e4Loop_exec {m' B₀ : ℕ} {Φ : ℕ → ℕ} (c₁ : Config) (hw : WordsBounded W c₁)
    (h924 : c₁.nreg 924 = B₀ + m') (h925 : c₁.nreg 925 = B₀ + 2 * m') (h918 : c₁.nreg 918 = m')
    (h917 : c₁.nreg 917 = 0) (h10 : c₁.nreg 10 = 1)
    (hΦ : ∀ i < m', c₁.nmem (B₀ + m' + i) = Φ i) (hΦlt : ∀ i < m', Φ i < m')
    (hinj : ∀ i < m', ∀ i' < m', Φ i = Φ i' → i = i') (lW : B₀ + 3 * m' ≤ W) :
    ∃ c' t, Exec P W (.whileLtN 917 918 e4Body) c₁ c' t ∧ t ≤ 7 * m' + 2 ∧
      (∀ i < m', c'.nmem (B₀ + 2 * m' + Φ i) = i) ∧
      (∀ a, (a < B₀ + 2 * m' ∨ B₀ + 3 * m' ≤ a) → c'.nmem a = c₁.nmem a) ∧
      (∀ r, r < 917 ∨ (917 < r ∧ r < 920) ∨ (920 < r ∧ r < 932) ∨ 932 < r →
        c'.nreg r = c₁.nreg r) ∧
      c'.rreg = c₁.rreg ∧ c'.rmem = c₁.rmem ∧ c'.output = c₁.output := by
  let J : ℕ → Config → Prop := fun i c' =>
    (∀ r, r < 917 ∨ (917 < r ∧ r < 920) ∨ (920 < r ∧ r < 932) ∨ 932 < r →
      c'.nreg r = c₁.nreg r) ∧
      c'.rreg = c₁.rreg ∧ c'.rmem = c₁.rmem ∧ c'.output = c₁.output ∧
      (∀ a, (a < B₀ + 2 * m' ∨ B₀ + 3 * m' ≤ a) → c'.nmem a = c₁.nmem a) ∧
      (∀ i' < i, c'.nmem (B₀ + 2 * m' + Φ i') = i')
  refine spec_use (forLoop_exec (P := P) (a := 917) (bR := 918) (body := e4Body) J (K := 5)
    (n := m') _ hw h917 h918 ?_ (fun i c₂ hi hw₂ ha hb ⟨fr, frr, frm, fo, fm, f1⟩ => ?_)) ?_
  · exact ⟨fun _ _ => rfl, rfl, rfl, rfl, fun _ _ => rfl, fun _ h => absurd h (by omega)⟩
  · have g924 : c₂.nreg 924 = B₀ + m' := by rw [fr 924 (by omega), h924]
    have g925 : c₂.nreg 925 = B₀ + 2 * m' := by rw [fr 925 (by omega), h925]
    have g10 : c₂.nreg 10 = 1 := by rw [fr 10 (by omega), h10]
    have gΦ : c₂.nmem (B₀ + m' + i) = Φ i := by rw [fm _ (by omega)]; exact hΦ i hi
    have hΦi := hΦlt i hi
    unfold e4Body
    exec_block
    all_goals try ((try config_simp); (try simp only [g924, g925, g10, ha, gΦ]) <;> omega)
    refine ⟨by omega, by config_simp; simp only [g10, ha], by config_simp; exact hb,
      fun r hr => ?_, frr, frm, fo, fun a ha' => ?_, fun i' hi' => ?_⟩
    · config_simp
      have h1 : r ≠ 917 := by omega
      have h2 : r ≠ 920 := by omega
      have h3 : r ≠ 932 := by omega
      simp only [upd_other _ _ _ h1, upd_other _ _ _ h2, upd_other _ _ _ h3]; exact fr r hr
    · config_simp; simp only [upd_apply, g924, g925, ha, gΦ]
      split_ifs <;> first | omega | exact fm a ha'
    · config_simp; simp only [upd_apply, g924, g925, ha, gΦ]
      by_cases e : i' = i
      · subst e; simp
      · have hne : Φ i' ≠ Φ i := fun h' => e (hinj i' (by omega) i hi h')
        split_ifs <;> first | omega | exact f1 i' (by omega)
  · intro c' t ht _ ⟨_, fr, frr, frm, fo, fm, f1⟩
    exact ⟨by omega, f1, fm, fr, frr, frm, fo⟩

/-- The arrays of the component: compaction, the reversal, the face permutation and the rotation
by ranks with the flags, the inverse of the face permutation. -/
def encPre : Stmt :=
  .seq (block [.addN 923 916 910, .constN 917 0, .constN 918 0]) <|
  .seq (.whileLtN 917 910 cmBody) <|
  .seq (block [.addN 924 915 918, .addN 925 924 918, .addN 926 925 918, .addN 927 926 918,
    .addN 928 927 918, .addN 929 923 910, .constN 917 0]) <|
  .seq (.whileLtN 917 918 e3Body) <|
  .seq (.instr (.constN 917 0)) (.whileLtN 917 918 e4Body)

/-- The vertex and face numbers by orbit labelling, and the registers `r390 … r393` of
`sepRun`. -/
def encOrb : Stmt :=
  .seq (block [.copyN 900 918, .copyN 901 929, .copyN 902 926]) <|
  .seq orbProg <|
  .seq (block [.copyN 933 905, .copyN 901 924, .copyN 902 927]) <|
  .seq orbProg <|
  block [.copyN 934 905, .copyN 390 918, .copyN 391 933, .copyN 392 934, .copyN 393 915]

/-- **The plain encoding of the piece map of the component**, from the plain encoding of the
piece and the flags of the component (`encPre ; encOrb`). -/
def encProg : Stmt := .seq encPre encOrb

lemma prk_congr {q q' : ℕ → Prop} [DecidablePred q] [DecidablePred q'] {n : ℕ}
    (h : ∀ x < n, (q x ↔ q' x)) : ∀ x ≤ n, prk q x = prk q' x := by
  intro x hx
  unfold prk
  congr 1
  ext y
  simp only [mem_filter, mem_range]
  exact ⟨fun ⟨h1, h2⟩ => ⟨h1, (h y (by omega)).1 h2⟩, fun ⟨h1, h2⟩ => ⟨h1, (h y (by omega)).2 h2⟩⟩

section Sem

open Orbit CombMap BKMNW PlanarSeparator PlanarSeparator.MillerProg

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {N : CombMap D V F}
variable {Pc : Finset D} {m k : ℕ} {δ : ℕ → D} {α σ : ℕ → ℕ}

lemma rcl_mono {K : Finset D} (hK : K ⊆ Pc) : rcl N K ⊆ rcl N Pc := fun e he => by
  rcases mem_rcl.1 he with h | h
  · exact mem_rcl.2 (Or.inl (hK h))
  · exact mem_rcl.2 (Or.inr (hK h))

/-- A dart of the piece whose reverse is in a share-closed part is in it. -/
lemma ShareClosed.of_rev {K : Finset D} (hK : ShareClosed N Pc K) {d : D} (hd : d ∈ Pc)
    (hr : N.rev d ∈ K) : d ∈ K :=
  hK.2 _ hr d hd (share_of (v := N.head d) (Or.inl (by rw [N.tail_rev])) (Or.inr rfl))

/-- The dart of the piece of a half-edge is in a share-closed part exactly when the half-edge is
in the piece map of the part. -/
theorem PEnc.udart_mem_iff (he : PEnc N Pc m k δ α σ) {K : Finset D} (hK : ShareClosed N Pc K)
    {h : ℕ} (hh : h < k) : δ (udart m α h) ∈ K ↔ δ h ∈ rcl N K := by
  unfold udart
  split_ifs with hm
  · refine ⟨fun h' => subset_rcl K h', fun h' => ?_⟩
    rcases mem_rcl.1 h' with h1 | h1
    · exact h1
    · exact hK.of_rev ((he.mem_iff hh).2 hm) h1
  · rw [he.α_eq h hh]
    refine ⟨fun h' => mem_rcl.2 (Or.inr h'), fun h' => ?_⟩
    rcases mem_rcl.1 h' with h1 | h1
    · exact absurd ((he.mem_iff hh).1 (hK.1 h1)) hm
    · exact h1

/-- A half-edge of the piece map of a share-closed part is a dart of the part exactly when it
is one of the piece. -/
theorem PEnc.lt_iff_mem (he : PEnc N Pc m k δ α σ) {K : Finset D} (hK : ShareClosed N Pc K)
    {h : ℕ} (hh : h < k) (hm : δ h ∈ rcl N K) : h < m ↔ δ h ∈ K := by
  refine ⟨fun h' => ?_, fun h' => (he.mem_iff hh).1 (hK.1 h')⟩
  have := (he.udart_mem_iff hK hh).2 hm
  rwa [udart_of_lt h'] at this

lemma Map.vert_eq_iff {D Q : Type*} [Finite D] (M : PlanarSeparator.Map D Q) {d d' : D} :
    M.vert d = M.vert d' ↔ M.σ.SameCycle d d' := by
  refine ⟨M.sameCycle d d', fun h => ?_⟩
  obtain ⟨n, rfl⟩ := h.exists_nat_pow_eq
  exact (M.vert_σ_pow n d).symm

lemma kmap_vert_surjective (K : Finset D) : Function.Surjective (kmap N K).vert := by
  intro v
  induction v using Quotient.inductionOn with
  | h x => exact ⟨x, pieceSep_vert _ _ x⟩

end Sem

set_option maxHeartbeats 4000000 in
/-- **The arrays of the component on the machine.** From the reversal `α` and the rotation `σ`
of the half-edges `h < k` of the piece, and flags of the darts read by a predicate `q` on the
half-edges (closed under `α` and `σ`, `σ ∘ α` injective), `encPre` writes, with `m' = prk q k`
the number of half-edges with `q`: the rank `prk q h` of every half-edge at `X + h`; for a
half-edge with `q` of rank `i`, the ranks of its reversal, of its image under `σ ∘ α` and under
`σ` at `B₀ + i`, `B₀ + m' + i`, `X + 2 k + i`, its flag `h < m` at `B₀ + 5 m' + i`; the
inverse of the array at `B₀ + m'` at `B₀ + 2 m'`. Within `16 k + 36 m' + 20` steps. -/
theorem encPre_exec {q : ℕ → Prop} [DecidablePred q] {k m bα bσ bF B₀ X : ℕ} {α σ : ℕ → ℕ}
    (c₀ : Config) (hc : WordsBounded W c₀) (h910 : c₀.nreg 910 = k) (h911 : c₀.nreg 911 = m)
    (h912 : c₀.nreg 912 = bα) (h913 : c₀.nreg 913 = bσ) (h914 : c₀.nreg 914 = bF)
    (h915 : c₀.nreg 915 = B₀) (h916 : c₀.nreg 916 = X) (h10 : c₀.nreg 10 = 1)
    (hα : ∀ h < k, c₀.nmem (bα + h) = α h) (hσ : ∀ h < k, c₀.nmem (bσ + h) = σ h)
    (hq : ∀ h < k, (c₀.nmem (bF + cmU m bα c₀.nmem h) ≠ 0 ↔ q h))
    (hu : ∀ h < k, cmU m bα c₀.nmem h < m)
    (hαk : ∀ h < k, α h < k) (hσk : ∀ h < k, σ h < k)
    (hqα : ∀ h < k, q h → q (α h)) (hqσ : ∀ h < k, q h → q (σ h))
    (hinj : ∀ h < k, ∀ h' < k, q h → q h' → σ (α h) = σ (α h') → h = h')
    (lα : bα + k ≤ B₀) (lσ : bσ + k ≤ B₀) (lF : bF + m ≤ B₀) (lB : B₀ + 6 * k ≤ X)
    (lW : X + 3 * k ≤ W) :
    ∃ c' t, Exec P W encPre c₀ c' t ∧ t ≤ 16 * k + 36 * prk q k + 20 ∧
      c'.nreg 918 = prk q k ∧ c'.nreg 924 = B₀ + prk q k ∧ c'.nreg 926 = B₀ + 3 * prk q k ∧
      c'.nreg 927 = B₀ + 4 * prk q k ∧ c'.nreg 929 = X + 2 * k ∧
      (∀ h < k, c'.nmem (X + h) = prk q h) ∧
      (∀ h < k, q h → c'.nmem (B₀ + prk q h) = prk q (α h) ∧
        c'.nmem (B₀ + prk q k + prk q h) = prk q (σ (α h)) ∧
        c'.nmem (X + 2 * k + prk q h) = prk q (σ h) ∧
        c'.nmem (B₀ + 5 * prk q k + prk q h) = if h < m then 1 else 0) ∧
      (∀ i < prk q k, c'.nmem (B₀ + 2 * prk q k + c'.nmem (B₀ + prk q k + i)) = i) ∧
      (∀ a, (a < B₀ ∨ (B₀ + 6 * prk q k ≤ a ∧ a < X) ∨ X + 3 * k ≤ a) → c'.nmem a = c₀.nmem a) ∧
      (∀ r, r < 917 ∨ 937 < r → c'.nreg r = c₀.nreg r) ∧
      c'.rreg = c₀.rreg ∧ c'.rmem = c₀.rmem ∧ c'.output = c₀.output := by
  set m' := prk q k with hm'
  have hmk : m' ≤ k := prk_le k
  -- setup
  obtain ⟨c₁, k₁, ex₁, hk₁, g923, g917, g918, gr₁, gm₁, grr₁, grm₁, go₁⟩ :
      ∃ c₁ k₁, Exec P W (block [.addN 923 916 910, .constN 917 0, .constN 918 0]) c₀ c₁ k₁ ∧
        k₁ = 3 ∧ c₁.nreg 923 = X + k ∧ c₁.nreg 917 = 0 ∧ c₁.nreg 918 = 0 ∧
        (∀ r, r ≠ 917 → r ≠ 918 → r ≠ 923 → c₁.nreg r = c₀.nreg r) ∧ c₁.nmem = c₀.nmem ∧
        c₁.rreg = c₀.rreg ∧ c₁.rmem = c₀.rmem ∧ c₁.output = c₀.output := by
    exec_block
    all_goals try ((try config_simp); (try simp only [h916, h910]) <;> omega)
    config_simp
    simp only [h916, h910]
    and_intros
    all_goals try omega
    all_goals try rfl
    all_goals try trivial
    intro r h1 h2 h3; simp [upd_apply, h1, h2, h3]
  have r₁ : ∀ r, r < 917 ∨ 923 < r → c₁.nreg r = c₀.nreg r := fun r hr =>
    gr₁ r (by omega) (by omega) (by omega)
  -- the compaction
  have hu₁ : ∀ h < k, cmU m bα c₁.nmem h < m := by rw [gm₁]; exact hu
  obtain ⟨c₂, k₂, ex₂, hk₂, f918, fI, fP, fm₂, fr₂, frr₂, frm₂, fo₂⟩ :=
    cmLoop_exec (P := P) c₁ ex₁.wb_right (by rw [r₁ 910 (by omega), h910])
      (by rw [r₁ 911 (by omega), h911]) (by rw [r₁ 912 (by omega), h912])
      (by rw [r₁ 914 (by omega), h914]) (by rw [r₁ 916 (by omega), h916]) g923
      (by rw [r₁ 10 (by omega), h10]) g917 g918 hu₁ (by omega) (by omega) (by omega)
  have hqq : ∀ h < k, (c₁.nmem (bF + cmU m bα c₁.nmem h) ≠ 0 ↔ q h) := by rw [gm₁]; exact hq
  have hrk := prk_congr hqq
  rw [hrk k le_rfl] at f918
  have fI' : ∀ h < k, c₂.nmem (X + h) = prk q h := fun h hh => by
    rw [fI h hh, hrk h hh.le]
  have fP' : ∀ h < k, q h → c₂.nmem (X + k + prk q h) = h := fun h hh hqh => by
    rw [← hrk h hh.le]; exact fP h hh ((hqq h hh).2 hqh)
  have r₂ : ∀ r, r < 917 ∨ 923 < r → c₂.nreg r = c₀.nreg r := fun r hr => by
    rw [fr₂ r (by omega), r₁ r hr]
  -- the bases
  have hw₂ := ex₂.wb_right
  obtain ⟨c₃, k₃, ex₃, hk₃, b924, b925, b926, b927, b928, b929, b917, gr₃, gm₃, grr₃, grm₃,
      go₃⟩ :
      ∃ c₃ k₃, Exec P W (block [.addN 924 915 918, .addN 925 924 918, .addN 926 925 918,
        .addN 927 926 918, .addN 928 927 918, .addN 929 923 910, .constN 917 0]) c₂ c₃ k₃ ∧
        k₃ = 7 ∧ c₃.nreg 924 = B₀ + m' ∧ c₃.nreg 925 = B₀ + 2 * m' ∧
        c₃.nreg 926 = B₀ + 3 * m' ∧ c₃.nreg 927 = B₀ + 4 * m' ∧ c₃.nreg 928 = B₀ + 5 * m' ∧
        c₃.nreg 929 = X + 2 * k ∧ c₃.nreg 917 = 0 ∧
        (∀ r, r < 917 ∨ (917 < r ∧ r < 924) ∨ 929 < r → c₃.nreg r = c₂.nreg r) ∧
        c₃.nmem = c₂.nmem ∧
        c₃.rreg = c₂.rreg ∧ c₃.rmem = c₂.rmem ∧ c₃.output = c₂.output := by
    have e915 : c₂.nreg 915 = B₀ := by rw [r₂ 915 (by omega), h915]
    have e923 : c₂.nreg 923 = X + k := by rw [fr₂ 923 (by omega), g923]
    have e910 : c₂.nreg 910 = k := by rw [r₂ 910 (by omega), h910]
    exec_block
    all_goals try ((try config_simp); (try simp only [e915, e923, e910, f918]) <;> omega)
    config_simp
    simp only [e915, e923, e910, f918]
    and_intros
    all_goals try omega
    all_goals try rfl
    all_goals try trivial
    intro r hr; simp only [upd_apply]; split_ifs <;> first | omega | rfl
  have r₃ : ∀ r, r < 917 ∨ 929 < r → c₃.nreg r = c₀.nreg r := fun r hr => by
    rw [gr₃ r (by omega), r₂ r (by omega)]
  -- the arrays of the component
  have hw₃ := ex₃.wb_right
  set pos : ℕ → ℕ := fun i => c₂.nmem (X + k + i) with hpos
  have hposeq : ∀ h < k, q h → pos (prk q h) = h := fun h hh hqh => fP' h hh hqh
  have hposq : ∀ i < m', pos i < k ∧ q (pos i) ∧ prk q (pos i) = i := fun i hi => by
    obtain ⟨h, hh, hqh, e⟩ := prk_surj (q := q) (k := k) hi
    rw [← e, hposeq h hh hqh]; exact ⟨hh, hqh, rfl⟩
  have m3α : ∀ h < k, c₃.nmem (bα + h) = α h := fun h hh => by
    rw [gm₃, fm₂ _ (by omega), gm₁]; exact hα h hh
  have m3σ : ∀ h < k, c₃.nmem (bσ + h) = σ h := fun h hh => by
    rw [gm₃, fm₂ _ (by omega), gm₁]; exact hσ h hh
  obtain ⟨c₄, k₄, ex₄, hk₄, o1, o2, o3, o4, fm₄, fr₄, frr₄, frm₄, fo₄⟩ :=
    e3Loop_exec (P := P) (pos := pos) (α := α) (σ := σ) (Ib := prk q) c₃ hw₃
      (by rw [r₃ 911 (by omega), h911]) (by rw [r₃ 912 (by omega), h912])
      (by rw [r₃ 913 (by omega), h913]) (by rw [r₃ 916 (by omega), h916])
      (by rw [gr₃ 923 (by omega), fr₂ 923 (by omega), g923]) (by rw [r₃ 915 (by omega), h915])
      b924 b929 b928 (by rw [gr₃ 918 (by omega), f918]) b917 (by rw [r₃ 10 (by omega), h10])
      (fun i _ => by rw [gm₃]) m3α m3σ (fun h hh => by rw [gm₃]; exact fI' h hh)
      (fun i hi => (hposq i hi).1) hαk hσk hmk lα lσ (by omega) lW
  -- the inverse of the face permutation
  have hw₄ := ex₄.wb_right
  have ex₅ := Exec.constN (P := P) hw₄ 917 0 (by omega)
  have hw₅ := ex₅.wb_right
  have hΦlt : ∀ i < m', prk q (σ (α (pos i))) < m' := fun i hi => by
    obtain ⟨hp, hqp, -⟩ := hposq i hi
    exact prk_lt (hqσ _ (hαk _ hp) (hqα _ hp hqp)) (hσk _ (hαk _ hp))
  have hΦinj : ∀ i < m', ∀ i' < m', prk q (σ (α (pos i))) = prk q (σ (α (pos i'))) → i = i' := by
    intro i hi i' hi' e
    obtain ⟨hp, hqp, ep⟩ := hposq i hi
    obtain ⟨hp', hqp', ep'⟩ := hposq i' hi'
    have := prk_inj (hqσ _ (hαk _ hp) (hqα _ hp hqp)) (hqσ _ (hαk _ hp') (hqα _ hp' hqp')) e
    rw [← ep, ← ep', hinj _ hp _ hp' hqp hqp' this]
  obtain ⟨c₆, k₆, ex₆, hk₆, i1, fm₆, fr₆, frr₆, frm₆, fo₆⟩ :=
    e4Loop_exec (P := P) (Φ := fun i => prk q (σ (α (pos i)))) _ hw₅
      (by config_simp; rw [fr₄ 924 (by omega), b924])
      (by config_simp; rw [fr₄ 925 (by omega)]; exact b925)
      (by config_simp; rw [fr₄ 918 (by omega), gr₃ 918 (by omega), f918])
      (by config_simp) (by config_simp; rw [fr₄ 10 (by omega), r₃ 10 (by omega), h10])
      (fun i hi => by config_simp; exact o2 i hi) hΦlt hΦinj (by omega)
  refine ⟨c₆, k₁ + (k₂ + (k₃ + (k₄ + (1 + k₆)))),
    Exec.seq ex₁ (Exec.seq ex₂ (Exec.seq ex₃ (Exec.seq ex₄ (Exec.seq ex₅ ex₆)))), ?_, ?_, ?_, ?_,
    ?_, ?_, fun h hh => ?_, fun h hh hqh => ?_, fun i hi => ?_, fun a ha => ?_, fun r hr => ?_,
    ?_, ?_, ?_⟩
  · have := prk_le (q := q) k; omega
  · rw [fr₆ 918 (by omega)]; config_simp; rw [fr₄ 918 (by omega), gr₃ 918 (by omega), f918]
  · rw [fr₆ 924 (by omega)]; config_simp; rw [fr₄ 924 (by omega), b924]
  · rw [fr₆ 926 (by omega)]; config_simp; rw [fr₄ 926 (by omega), b926]
  · rw [fr₆ 927 (by omega)]; config_simp; rw [fr₄ 927 (by omega), b927]
  · rw [fr₆ 929 (by omega)]; config_simp; rw [fr₄ 929 (by omega), b929]
  · rw [fm₆ _ (by omega)]; config_simp
    rw [fm₄ _ (by unfold E3Fr; omega), gm₃]; exact fI' h hh
  · have hi := prk_lt (q := q) hqh hh
    have e := hposeq h hh hqh
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [fm₆ _ (by omega)]; config_simp; rw [o1 _ hi, e]
    · rw [fm₆ _ (by omega)]; config_simp; rw [o2 _ hi, e]
    · rw [fm₆ _ (by omega)]; config_simp; rw [o3 _ hi, e]
    · rw [fm₆ _ (by omega)]; config_simp; rw [o4 _ hi, e]
  · have e : c₆.nmem (B₀ + m' + i) = prk q (σ (α (pos i))) := by
      rw [fm₆ _ (by omega)]; config_simp; exact o2 i hi
    rw [e]; exact i1 i hi
  · rw [fm₆ _ (by omega)]; config_simp
    rw [fm₄ _ (by unfold E3Fr; omega), gm₃, fm₂ _ (by omega), gm₁]
  · rw [fr₆ r (by omega)]; config_simp
    rw [upd_other _ _ _ (show r ≠ 917 by omega), fr₄ r (by omega), r₃ r (by omega)]
  · rw [frr₆]; config_simp; rw [frr₄, grr₃, frr₂, grr₁]
  · rw [frm₆]; config_simp; rw [frm₄, grm₃, frm₂, grm₁]
  · rw [fo₆]; config_simp; rw [fo₄, go₃, fo₂, go₁]

section Main

open Orbit CombMap BKMNW PlanarSeparator PlanarSeparator.MillerProg

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {N : CombMap D V F}
variable {Pc : Finset D} {m k : ℕ} {δ : ℕ → D} {α σ : ℕ → ℕ}

set_option maxHeartbeats 4000000 in
/-- **The plain encoding of the piece map of a component, on the machine.** From the plain
encoding of the piece `Pc` carrying its own rotation (`PEnc`: the reversal `α` at `bα`, the
rotation `σ` at `bσ`, `k` half-edges of which the `m` darts of `Pc` come first) and flags `F`
at `bF` of the darts of a share-closed part `K` (a component: `compProg_spec`, `flags_big`),
`encProg` writes within `116 k + 47` steps the plain encoding `Enc` of the piece map
`kmap N K` at `B₀` (darts numbered by `c`, by rank among the half-edges of `K`, `m'` of them;
`nV` vertices, `nF` faces), the flags `flK` at `B₀ + 5 m'`, the registers `r390 … r393` of
`sepRun`, and the index `c` of every half-edge of `K` at `X + h` (the index array of
`joinProg`). -/
theorem encProg_enc (he : PEnc N Pc m k δ α σ) {K : Finset D} (hK : ShareClosed N Pc K)
    {Fl : ℕ → ℕ} (hF : ∀ x < m, (Fl x ≠ 0 ↔ δ x ∈ K)) {bα bσ bF B₀ X : ℕ} (c₀ : Config)
    (hc : WordsBounded W c₀) (h910 : c₀.nreg 910 = k) (h911 : c₀.nreg 911 = m)
    (h912 : c₀.nreg 912 = bα) (h913 : c₀.nreg 913 = bσ) (h914 : c₀.nreg 914 = bF)
    (h915 : c₀.nreg 915 = B₀) (h916 : c₀.nreg 916 = X) (h10 : c₀.nreg 10 = 1)
    (hα : ∀ h < k, c₀.nmem (bα + h) = α h) (hσ : ∀ h < k, c₀.nmem (bσ + h) = σ h)
    (hFm : ∀ x < m, c₀.nmem (bF + x) = Fl x)
    (lα : bα + k ≤ B₀) (lσ : bσ + k ≤ B₀) (lF : bF + m ≤ B₀) (lB : B₀ + 6 * k ≤ X)
    (lW : X + 3 * k + 2 ≤ W) :
    ∃ c' t, Exec P W encProg c₀ c' t ∧ t ≤ 116 * k + 47 ∧
      ∃ (m' nV nF : ℕ) (c : SDart (rcl N K) ≃ Fin m') (vn : SVert (kσ N K) (rcl N K) ≃ Fin nV)
        (fn : (kmap N K).Face ≃ Fin nF),
        Enc (kmap N K) c vn fn c'.nmem B₀ (B₀ + m') (B₀ + 2 * m') (B₀ + 3 * m') (B₀ + 4 * m') ∧
        (∀ d, c'.nmem (B₀ + 5 * m' + c d) = flK N K d) ∧
        c'.nreg 390 = m' ∧ c'.nreg 391 = nV ∧ c'.nreg 392 = nF ∧ c'.nreg 393 = B₀ ∧ m' ≤ k ∧
        (∀ h < k, ∀ hm : δ h ∈ rcl N K, c'.nmem (X + h) = c ⟨δ h, hm⟩) ∧
        (∀ a, (a < B₀ ∨ (B₀ + 6 * m' ≤ a ∧ a < X) ∨ X + 3 * k ≤ a) → c'.nmem a = c₀.nmem a) ∧
        (∀ r, r < 390 ∨ (393 < r ∧ r < 900) ∨ (908 < r ∧ r < 917) ∨ 937 < r →
          c'.nreg r = c₀.nreg r) ∧
        c'.rreg = c₀.rreg ∧ c'.rmem = c₀.rmem ∧ c'.output = c₀.output := by
  have hmk := he.mle
  set q : ℕ → Prop := fun h => δ h ∈ rcl N K with hqdef
  have hU : ∀ h < k, cmU m bα c₀.nmem h = udart m α h := fun h hh => by
    unfold cmU udart; split_ifs
    · rfl
    · exact hα h hh
  have hq : ∀ h < k, (c₀.nmem (bF + cmU m bα c₀.nmem h) ≠ 0 ↔ q h) := fun h hh => by
    rw [hU h hh, hFm _ (he.udart_lt hh), hF _ (he.udart_lt hh), he.udart_mem_iff hK hh]
  have hu : ∀ h < k, cmU m bα c₀.nmem h < m := fun h hh => by
    rw [hU h hh]; exact he.udart_lt hh
  have hqα : ∀ h < k, q h → q (α h) := fun h hh hqh => by
    change δ (α h) ∈ rcl N K
    rw [he.α_eq h hh]; exact rcl_stable K _ hqh
  have hqσ : ∀ h < k, q h → q (σ h) := fun h hh hqh => by
    change δ (σ h) ∈ rcl N K
    rw [he.σ_eq_comp hK hh hqh]; exact ret_mem hqh
  have hinj : ∀ h < k, ∀ h' < k, q h → q h' → σ (α h) = σ (α h') → h = h' := by
    intro h hh h' hh' _ _ e
    have e1 := he.hEnc.σ_inj _ (he.α_lt h hh) _ (he.α_lt h' hh') e
    rw [← he.hEnc.αα h hh, ← he.hEnc.αα h' hh', e1]
  obtain ⟨c₁, k₁, ex₁, hk₁, g918, g924, g926, g927, g929, gI, gO, gΦi, gm₁, gr₁, grr₁, grm₁,
      go₁⟩ :=
    encPre_exec (P := P) (q := q) c₀ hc h910 h911 h912 h913 h914 h915 h916 h10 hα hσ hq hu
      he.α_lt he.σ_lt hqα hqσ hinj lα lσ lF lB (by omega)
  set m' := prk q k with hm'
  have hm'k : m' ≤ k := prk_le k
  obtain ⟨c, hc'⟩ := exists_rank_equiv (q := q) he.enum (rcl_mono hK.1) (fun h _ => Iff.rfl)
  -- the darts of the piece map through their half-edges
  have hcd : ∀ d : SDart (rcl N K), ∃ h < k, δ h = d.1 ∧ q h ∧ (c d : ℕ) = prk q h := by
    intro d
    obtain ⟨h, hh, e⟩ := he.enum.surj _ (rcl_mono hK.1 d.2)
    have hq' : q h := by change δ h ∈ rcl N K; rw [e]; exact d.2
    refine ⟨h, hh, e, hq', ?_⟩
    rw [← hc' h hh hq']; congr 2; exact Subtype.ext e.symm
  have hcq : ∀ h < k, ∀ hq' : q h, (c ⟨δ h, hq'⟩ : ℕ) = prk q h := fun h hh hq' => hc' h hh hq'
  have eα : ∀ d, c₁.nmem (B₀ + c d) = c ((kmap N K).α d) := by
    intro d
    obtain ⟨h, hh, e, hqh, hcdh⟩ := hcd d
    rw [hcdh, (gO h hh hqh).1, ← hcq _ (he.α_lt h hh) (hqα h hh hqh)]
    congr 2; apply Subtype.ext
    rw [pieceSep_α]; show δ (α h) = _; rw [he.α_eq h hh, e]
  have eφ : ∀ d, c₁.nmem (B₀ + m' + c d) = c ((kmap N K).φ d) := by
    intro d
    obtain ⟨h, hh, e, hqh, hcdh⟩ := hcd d
    rw [hcdh, (gO h hh hqh).2.1,
      ← hcq _ (he.σ_lt _ (he.α_lt h hh)) (hqσ _ (he.α_lt h hh) (hqα h hh hqh))]
    congr 2; apply Subtype.ext
    rw [pieceSep_φ]; show δ (σ (α h)) = _
    rw [he.σ_eq_comp hK (he.α_lt h hh) (hqα h hh hqh), he.α_eq h hh, e]
  have eS : ∀ d, c₁.nmem (X + 2 * k + c d) = c ((kmap N K).σ d) := by
    intro d
    obtain ⟨h, hh, e, hqh, hcdh⟩ := hcd d
    rw [hcdh, (gO h hh hqh).2.2.1, ← hcq _ (he.σ_lt h hh) (hqσ h hh hqh)]
    congr 2; apply Subtype.ext
    rw [pieceSep_σ]; show δ (σ h) = _; rw [he.σ_eq_comp hK hh hqh, e]
  have eFl : ∀ d, c₁.nmem (B₀ + 5 * m' + c d) = flK N K d := by
    intro d
    obtain ⟨h, hh, e, hqh, hcdh⟩ := hcd d
    rw [hcdh, (gO h hh hqh).2.2.2]
    unfold flK
    have := he.lt_iff_mem hK hh hqh
    rw [e] at this
    by_cases h1 : h < m
    · simp [h1, this.1 h1]
    · simp [h1, mt this.2 h1]
  have eφi : ∀ d, c₁.nmem (B₀ + 2 * m' + c d) = c ((kmap N K).φ.symm d) := by
    intro d
    have := gΦi _ (c ((kmap N K).φ.symm d)).isLt
    rwa [eφ, Equiv.apply_symm_apply] at this
  -- the vertex numbers
  have hw₁ := ex₁.wb_right
  obtain ⟨c₂, k₂, ex₂, hk₂, a900, a901, a902, ar₂, am₂, arr₂, arm₂, ao₂⟩ :
      ∃ c₂ k₂, Exec P W (block [.copyN 900 918, .copyN 901 929, .copyN 902 926]) c₁ c₂ k₂ ∧
        k₂ = 3 ∧ c₂.nreg 900 = m' ∧ c₂.nreg 901 = X + 2 * k ∧ c₂.nreg 902 = B₀ + 3 * m' ∧
        (∀ r, r < 900 ∨ 902 < r → c₂.nreg r = c₁.nreg r) ∧ c₂.nmem = c₁.nmem ∧
        c₂.rreg = c₁.rreg ∧ c₂.rmem = c₁.rmem ∧ c₂.output = c₁.output := by
    exec_block
    config_simp
    simp only [g918, g929, g926]
    and_intros
    all_goals try rfl
    all_goals try trivial
    intro r hr; simp only [upd_apply]; split_ifs <;> first | omega | rfl
  obtain ⟨c₃, k₃, ex₃, hk₃, vlt, veq, vsurj, vr₃, vrr₃, vrm₃, vo₃, vm₃⟩ :=
    orbProg_exec (P := P) (π := (kmap N K).σ) (e := c) (bp := X + 2 * k) (bL := B₀ + 3 * m')
      c₂ ex₂.wb_right a900 a901 a902 (by rw [ar₂ 10 (by omega), gr₁ 10 (by omega), h10])
      (fun t => by rw [am₂]; exact eS t) (Or.inr (by omega)) (by omega) (by omega) (by omega)
  -- the face numbers
  have hw₃ := ex₃.wb_right
  obtain ⟨c₄, k₄, ex₄, hk₄, b933, b901, b902, br₄, bm₄, brr₄, brm₄, bo₄⟩ :
      ∃ c₄ k₄, Exec P W (block [.copyN 933 905, .copyN 901 924, .copyN 902 927]) c₃ c₄ k₄ ∧
        k₄ = 3 ∧ c₄.nreg 933 = c₃.nreg 905 ∧ c₄.nreg 901 = B₀ + m' ∧
        c₄.nreg 902 = B₀ + 4 * m' ∧
        (∀ r, r ≠ 901 → r ≠ 902 → r ≠ 933 → c₄.nreg r = c₃.nreg r) ∧ c₄.nmem = c₃.nmem ∧
        c₄.rreg = c₃.rreg ∧ c₄.rmem = c₃.rmem ∧ c₄.output = c₃.output := by
    have e924 : c₃.nreg 924 = B₀ + m' := by rw [vr₃ 924 (by omega), ar₂ 924 (by omega), g924]
    have e927 : c₃.nreg 927 = B₀ + 4 * m' := by
      rw [vr₃ 927 (by omega), ar₂ 927 (by omega), g927]
    exec_block
    config_simp
    simp only [e924, e927]
    and_intros
    all_goals try rfl
    all_goals try trivial
    intro r h1 h2 h3; simp [upd_apply, h1, h2, h3]
  obtain ⟨c₅, k₅, ex₅, hk₅, flt, feq, fsurj, fr₅, frr₅, frm₅, fo₅, fm₅⟩ :=
    orbProg_exec (P := P) (π := (kmap N K).φ) (e := c) (bp := B₀ + m') (bL := B₀ + 4 * m')
      c₄ ex₄.wb_right (by rw [br₄ 900 (by omega) (by omega) (by omega), vr₃ 900 (by omega), a900])
      b901 b902
      (by rw [br₄ 10 (by omega) (by omega) (by omega), vr₃ 10 (by omega),
        ar₂ 10 (by omega), gr₁ 10 (by omega), h10])
      (fun t => by
        rw [bm₄, vm₃ _ (by have := (c t).isLt; omega), am₂]; exact eφ t)
      (Or.inl (by omega)) (by omega) (by omega) (by omega)
  -- the registers of `sepRun`
  have hw₅ := ex₅.wb_right
  obtain ⟨c₆, k₆, ex₆, hk₆, d390, d391, d392, d393, dr₆, dm₆, drr₆, drm₆, do₆⟩ :
      ∃ c₆ k₆, Exec P W (block [.copyN 934 905, .copyN 390 918, .copyN 391 933,
        .copyN 392 934, .copyN 393 915]) c₅ c₆ k₆ ∧
        k₆ = 5 ∧ c₆.nreg 390 = m' ∧ c₆.nreg 391 = c₃.nreg 905 ∧ c₆.nreg 392 = c₅.nreg 905 ∧
        c₆.nreg 393 = B₀ ∧
        (∀ r, r < 390 ∨ (393 < r ∧ r < 934) ∨ 934 < r → c₆.nreg r = c₅.nreg r) ∧
        c₆.nmem = c₅.nmem ∧
        c₆.rreg = c₅.rreg ∧ c₆.rmem = c₅.rmem ∧ c₆.output = c₅.output := by
    have e918 : c₅.nreg 918 = m' := by
      rw [fr₅ 918 (by omega), br₄ 918 (by omega) (by omega) (by omega), vr₃ 918 (by omega),
        ar₂ 918 (by omega), g918]
    have e933 : c₅.nreg 933 = c₃.nreg 905 := by rw [fr₅ 933 (by omega), b933]
    have e915 : c₅.nreg 915 = B₀ := by
      rw [fr₅ 915 (by omega), br₄ 915 (by omega) (by omega) (by omega), vr₃ 915 (by omega),
        ar₂ 915 (by omega), gr₁ 915 (by omega), h915]
    exec_block
    config_simp
    simp only [e918, e933, e915]
    and_intros
    all_goals try rfl
    all_goals try trivial
    intro r hr; simp only [upd_apply]; split_ifs <;> first | omega | rfl
  -- the numberings of the vertices and the faces
  obtain ⟨vn, hvn⟩ := exists_equiv_of_lab (q := (kmap N K).vert) (kmap_vert_surjective K)
    (lab := fun t => c₃.nmem (B₀ + 3 * m' + c t)) vlt
    (fun t t' => (veq t t').trans (Map.vert_eq_iff _).symm) vsurj
  obtain ⟨fn, hfn⟩ := exists_equiv_of_lab (q := (kmap N K).face) (kmap N K).face_surjective
    (lab := fun t => c₅.nmem (B₀ + 4 * m' + c t)) flt
    (fun t t' => (feq t t').trans (kmap N K).face_eq_face_iff.symm) fsurj
  -- the memory read back
  have back : ∀ a, (a < B₀ + 3 * m' ∨ B₀ + 5 * m' ≤ a) → c₆.nmem a = c₁.nmem a := by
    intro a ha
    rw [dm₆, fm₅ _ (by omega), bm₄, vm₃ _ (by omega), am₂]
  refine ⟨c₆, k₁ + (k₂ + (k₃ + (k₄ + (k₅ + k₆)))),
    by unfold encProg encOrb; exact Exec.seq ex₁ (Exec.seq ex₂ (Exec.seq ex₃ (Exec.seq ex₄
      (Exec.seq ex₅ ex₆)))), by omega, m', c₃.nreg 905, c₅.nreg 905, c, vn, fn,
    ⟨fun d => ?_, fun d => ?_, fun d => ?_, fun d => ?_, fun d => ?_⟩, fun d => ?_,
    d390, d391, d392, d393, hm'k, fun h hh hm => ?_, fun a ha => ?_, fun r hr => ?_, ?_, ?_, ?_⟩
  · rw [back _ (by have := (c d).isLt; omega)]; exact eα d
  · rw [back _ (by have := (c d).isLt; omega)]; exact eφ d
  · rw [back _ (by have := (c d).isLt; omega)]; exact eφi d
  · rw [dm₆, fm₅ _ (by have := (c d).isLt; omega), bm₄]; exact (hvn d).symm
  · rw [dm₆]; exact (hfn d).symm
  · rw [back _ (by omega)]; exact eFl d
  · rw [back _ (by omega), gI h hh]; exact (hcq h hh hm).symm
  · rw [back _ (by omega)]; exact gm₁ a ha
  · rw [dr₆ r (by omega), fr₅ r (by omega), br₄ r (by omega) (by omega) (by omega),
      vr₃ r (by omega), ar₂ r (by omega), gr₁ r (by omega)]
  · rw [drr₆, frr₅, brr₄, vrr₃, arr₂, grr₁]
  · rw [drm₆, frm₅, brm₄, vrm₃, arm₂, grm₁]
  · rw [do₆, fo₅, bo₄, vo₃, ao₂, go₁]

end Main

end NegSSSP

end PlanarFlow
