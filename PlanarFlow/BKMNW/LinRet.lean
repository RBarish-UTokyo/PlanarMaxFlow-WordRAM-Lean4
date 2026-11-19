module

public import PlanarFlow.BKMNW.PieceMap
public import PlanarFlow.BKMNW.LinLoops

/-!
# First returns on the machine, by deleting elements from a doubly linked cycle structure

The rotation of a child piece map is a first return (`PlanarFlow.BKMNW.childRot σ B L Bc =
ret (con ι σ (B \ L)) Bc`, `con ι σ B' = ret (σ ι) B' ι`). A first return `ret π A` is computed
here in linear time **without inner loops**: keep `π` restricted to a set `R` as two arrays
(`NX` the successor, `PR` the predecessor) and delete the elements outside `A` one by one
(`PR[s] := p`, `NX[p] := s` for the predecessor `p` and successor `s` of the deleted element).
Deleting `y` from `R` turns `ret π R` into `ret π (R \ {y})` (`ret_erase_eq`, with
`Orbit.ret_ret`).

* `ret_erase_eq`, `ret_symm_mem` (the inverse of a first return keeps its set), `RetRep` (the
  arrays represent `ret G R` and its inverse on the indices of `R`), **`retRep_erase`** (one
  deletion), `dset` (the set left after deleting the flagged indices below `i`), `dset_succ`.
* **`ldProg`** (registers `6240 = m`, `6241 = DFb`, `6242 = NXb`, `6243 = PRb`; scratch
  `6244 … 6250`): delete the indices `i < m` with `DF[i] > 0`; **`ldProg_exec`**: within
  `14 m + 5` steps, `RetRep e m G (dset e DF R m)` from `RetRep e m G R`.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace PlanarFlow

namespace BKMNW

open Finset Function Equiv Orbit WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

section Math

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- **Deleting one element from a stable set**: the first return skips it. -/
theorem ret_erase_eq {π : Perm α} {R : Finset α} (hR : Stable π R) {x y : α} (hx : x ∈ R)
    (hy : y ∈ R) (hxy : x ≠ y) :
    ret π (R.erase y) x = if π x = y then π y else π x := by
  have hxe : x ∈ R.erase y := mem_erase.2 ⟨hxy, hx⟩
  by_cases h : π x = y
  · rw [iteT h]
    have hyy : π y ≠ y := fun h' => hxy (π.injective (h.trans h'.symm))
    have e2 : (⇑π)^[2] x = π y := by
      rw [show (2 : ℕ) = 1 + 1 from rfl, iterate_succ_apply', iterate_one, h]
    rw [ret_eq_of hxe (n := 2) (by norm_num) (by rw [e2]; exact mem_erase.2 ⟨hyy, hR _ hy⟩)
      (fun k h0 h1 => by
        obtain rfl : k = 1 := by omega
        rw [iterate_one, h]; exact notMem_erase _ _), e2]
  · rw [iteF h]
    exact ret_eq_self_of hxe (mem_erase.2 ⟨h, hR _ hx⟩)

/-- The inverse of a first return keeps its set. -/
lemma ret_symm_mem {π : Perm α} {R : Finset α} {y : α} (hy : y ∈ R) :
    (ret π R).symm y ∈ R := by
  by_contra h
  have := ret_apply_of_not_mem (π := π) h
  rw [Equiv.apply_symm_apply] at this
  exact h (this ▸ hy)

/-- **The arrays represent a first return**: for every index `i < m` of an element of `R`, the
successor `NX[i]` and the predecessor `PR[i]` are indices below `m` of `ret G R (e i)` and of
its inverse. -/
def RetRep (e : ℕ → α) (m : ℕ) (G : Perm α) (R : Finset α) (mem : ℕ → ℕ) (NXb PRb : ℕ) :
    Prop :=
  ∀ i < m, e i ∈ R → mem (NXb + i) < m ∧ mem (PRb + i) < m ∧
    e (mem (NXb + i)) = ret G R (e i) ∧ e (mem (PRb + i)) = (ret G R).symm (e i)

/-- **One deletion**: with `p = PR[i]`, `s = NX[i]`, the arrays with `NX[p] := s` and
`PR[s] := p` represent `ret G (R \ {e i})`. -/
theorem retRep_erase {e : ℕ → α} {m : ℕ} {G : Perm α} {R : Finset α} {mem mem' : ℕ → ℕ}
    {NXb PRb : ℕ} (he : ∀ i < m, ∀ j < m, e i = e j → i = j)
    (h : RetRep e m G R mem NXb PRb) {i : ℕ} (hi : i < m) (hR : e i ∈ R)
    (hnx : ∀ j < m, mem' (NXb + j) =
      if j = mem (PRb + i) then mem (NXb + i) else mem (NXb + j))
    (hpr : ∀ j < m, mem' (PRb + j) =
      if j = mem (NXb + i) then mem (PRb + i) else mem (PRb + j)) :
    RetRep e m G (R.erase (e i)) mem' NXb PRb := by
  set π := ret G R with hπ
  have hst : Stable π R := stable_ret G R
  have hπ' : ret G (R.erase (e i)) = ret π (R.erase (e i)) :=
    (ret_ret (erase_subset _ _)).symm
  obtain ⟨hs, hp, hes, hep⟩ := h i hi hR
  set p := mem (PRb + i) with hpdef
  set s := mem (NXb + i) with hsdef
  have hpy : π (e p) = e i := by rw [hep, Equiv.apply_symm_apply]
  intro j hj hjR
  obtain ⟨hjy, hjR'⟩ := mem_erase.1 hjR
  obtain ⟨hs', hp', hes', hep'⟩ := h j hj hjR'
  rw [hnx j hj, hpr j hj, hπ']
  refine ⟨by split_ifs <;> assumption, by split_ifs <;> assumption, ?_, ?_⟩
  · rw [ret_erase_eq hst hjR' hR hjy]
    by_cases hjp : j = p
    · subst hjp
      rw [iteT rfl, iteT hpy]; exact hes
    · have hne : π (e j) ≠ e i := fun h' => hjp (he j hj p hp (by
        rw [hep, ← h', Equiv.symm_apply_apply]))
      rw [iteF hjp, iteF hne]; exact hes'
  · rw [Equiv.eq_symm_apply]
    by_cases hjs : j = s
    · subst hjs
      rw [iteT rfl]
      have hz : e p ∈ R := by rw [hep]; exact ret_symm_mem hR
      have hzy : e p ≠ e i := fun h' => hjy (by
        rw [hes]; show π (e i) = e i; rw [← h', hpy, h'])
      rw [ret_erase_eq hst hz hR hzy, iteT hpy]; exact hes.symm
    · rw [iteF hjs]
      have hz : e (mem (PRb + j)) ∈ R := by rw [hep']; exact ret_symm_mem hjR'
      have hpj : π (e (mem (PRb + j))) = e j := by rw [hep', Equiv.apply_symm_apply]
      have hzy : e (mem (PRb + j)) ≠ e i := fun h' => hjs (he j hj s hs (by
        rw [hes, ← h', hpj]))
      rw [ret_erase_eq hst hz hR hzy, hpj, iteF hjy]

/-- The set left after deleting the indices `j < i` with `DF j > 0`. -/
def dset (e : ℕ → α) (DF : ℕ → ℕ) (R : Finset α) (i : ℕ) : Finset α :=
  R.filter fun d => ∀ j < i, 0 < DF j → e j ≠ d

lemma dset_zero (e : ℕ → α) (DF : ℕ → ℕ) (R : Finset α) : dset e DF R 0 = R := by
  ext d; simp [dset]

lemma dset_succ (e : ℕ → α) (DF : ℕ → ℕ) (R : Finset α) (i : ℕ) :
    dset e DF R (i + 1) = if 0 < DF i then (dset e DF R i).erase (e i) else dset e DF R i := by
  by_cases h : 0 < DF i
  · rw [iteT h]
    ext d
    simp only [dset, mem_filter, mem_erase]
    constructor
    · rintro ⟨hd, hj⟩
      exact ⟨(hj i (by omega) h).symm, hd, fun j hj' => hj j (by omega)⟩
    · rintro ⟨hne, hd, hj⟩
      refine ⟨hd, fun j hj' hpos => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj' with hj' | rfl
      · exact hj j hj' hpos
      · exact fun h' => hne h'.symm
  · rw [iteF h]
    ext d
    simp only [dset, mem_filter]
    constructor
    · rintro ⟨hd, hj⟩
      exact ⟨hd, fun j hj' => hj j (by omega)⟩
    · rintro ⟨hd, hj⟩
      refine ⟨hd, fun j hj' hpos => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj' with hj' | rfl
      · exact hj j hj' hpos
      · exact absurd hpos h

lemma mem_dset_of {e : ℕ → α} {DF : ℕ → ℕ} {R : Finset α} {i : ℕ} (hi : e i ∈ R)
    (he : ∀ j < i, e j ≠ e i) : e i ∈ dset e DF R i :=
  mem_filter.2 ⟨hi, fun j hj _ => he j hj⟩

end Math

/-! ### The deletion loop -/

section Exec

variable {P : Input} {W : ℕ}

/-- The deletion of index `i` (`r6245`): `p := PR[i]`, `s := NX[i]`, `NX[p] := s`,
`PR[s] := p`. -/
def ldDel : Stmt :=
  block [.addN 6249 6243 6245, .loadN 6247 6249, .addN 6249 6242 6245, .loadN 6248 6249,
    .addN 6249 6242 6247, .storeN 6249 6248, .addN 6249 6243 6248, .storeN 6249 6247]

/-- One iteration: delete `i` if `DF[i] > 0`, then `i := i + 1`. -/
def ldBody : Stmt :=
  .seq (block [.addN 6249 6241 6245, .loadN 6246 6249])
    (.seq (.ifLtN 6250 6246 ldDel .skip) (block [.addN 6245 6245 6244]))

/-- **The deletion loop**: delete the indices `i < m` with `DF[i] > 0`. -/
def ldProg : Stmt :=
  .seq (block [.constN 6244 1, .constN 6245 0, .constN 6250 0]) (.whileLtN 6245 6240 ldBody)

theorem ldDel_exec (c : Config) (hc : WordsBounded W c) {NXb PRb i : ℕ}
    (r2 : c.nreg 6242 = NXb) (r3 : c.nreg 6243 = PRb) (r5 : c.nreg 6245 = i)
    (w1 : PRb + i ≤ W) (w2 : NXb + i ≤ W) (w3 : NXb + c.nmem (PRb + i) ≤ W)
    (w4 : PRb + c.nmem (NXb + i) ≤ W) :
    ∃ c' k, Exec P W ldDel c c' k ∧ k = 8 ∧
      c'.nmem = upd (upd c.nmem (NXb + c.nmem (PRb + i)) (c.nmem (NXb + i)))
        (PRb + c.nmem (NXb + i)) (c.nmem (PRb + i)) ∧
      (∀ x, (x < 6247 ∨ 6249 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold ldDel
  exec_block
  all_goals try (config_simp; simp only [r2, r3, r5]; omega)
  refine ⟨rfl, ?_, fun x hx => ?_, rfl, rfl, rfl⟩
  · config_simp; simp only [r2, r3, r5]
  · config_simp; simp only [upd_apply]; split_ifs <;> omega

theorem ldBody_exec (c : Config) (hc : WordsBounded W c) {DFb NXb PRb i : ℕ}
    (r1 : c.nreg 6241 = DFb) (r2 : c.nreg 6242 = NXb) (r3 : c.nreg 6243 = PRb)
    (r4 : c.nreg 6244 = 1) (r5 : c.nreg 6245 = i) (r0 : c.nreg 6250 = 0)
    (w0 : DFb + i ≤ W) (w1 : PRb + i ≤ W) (w2 : NXb + i ≤ W)
    (w3 : 0 < c.nmem (DFb + i) → NXb + c.nmem (PRb + i) ≤ W ∧ PRb + c.nmem (NXb + i) ≤ W)
    (w4 : i + 1 ≤ W) :
    ∃ c' k, Exec P W ldBody c c' k ∧ k ≤ 12 ∧ c'.nreg 6245 = i + 1 ∧
      c'.nmem = (if 0 < c.nmem (DFb + i) then
        upd (upd c.nmem (NXb + c.nmem (PRb + i)) (c.nmem (NXb + i)))
          (PRb + c.nmem (NXb + i)) (c.nmem (PRb + i)) else c.nmem) ∧
      (∀ x, (x < 6245 ∨ 6249 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold ldBody
  obtain ⟨c₁, k₁, e₁, hk₁, g6, gn₁, gm₁, gr₁, grm₁, go₁⟩ : ∃ c₁ k₁,
      Exec P W (block [.addN 6249 6241 6245, .loadN 6246 6249]) c c₁ k₁ ∧ k₁ = 2 ∧
      c₁.nreg 6246 = c.nmem (DFb + i) ∧
      (∀ x, x ≠ 6246 → x ≠ 6249 → c₁.nreg x = c.nreg x) ∧ c₁.nmem = c.nmem ∧
      c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    exec_block
    all_goals try (config_simp; simp only [r1, r5]; omega)
    refine ⟨rfl, ?_, fun x a b => ?_, rfl, rfl, rfl, rfl⟩
    · config_simp; simp only [r1, r5]
    · config_simp; simp only [upd_apply]; split_ifs <;> omega
  have hw₁ := e₁.wb_right
  have q1 : ∀ x, x ≠ 6246 → x ≠ 6249 → c₁.nreg x = c.nreg x := gn₁
  have inc : ∀ d : Config, WordsBounded W d → d.nreg 6245 = i → d.nreg 6244 = 1 →
      ∃ d' k, Exec P W (block [.addN 6245 6245 6244]) d d' k ∧ k = 1 ∧ d'.nreg 6245 = i + 1 ∧
        (∀ x, x ≠ 6245 → d'.nreg x = d.nreg x) ∧ d'.nmem = d.nmem ∧ d'.rreg = d.rreg ∧
        d'.rmem = d.rmem ∧ d'.output = d.output := fun d hd s5 s4 => by
    exec_block
    all_goals try (config_simp; simp only [s4, s5]; omega)
    refine ⟨rfl, ?_, fun x a => ?_, rfl, rfl, rfl, rfl⟩
    · config_simp; simp only [s4, s5]
    · config_simp; simp only [upd_apply]; split_ifs <;> omega
  by_cases hs : 0 < c.nmem (DFb + i)
  · obtain ⟨c₂, k₂, e₂, hk₂, gm₂, gn₂, gr₂, grm₂, go₂⟩ := ldDel_exec (P := P) c₁ hw₁
      (by rw [q1 _ (by omega) (by omega), r2]) (by rw [q1 _ (by omega) (by omega), r3])
      (by rw [q1 _ (by omega) (by omega), r5]) w1 w2 (by rw [gm₁]; exact (w3 hs).1)
      (by rw [gm₁]; exact (w3 hs).2)
    rw [gm₁] at gm₂
    obtain ⟨c₃, k₃, e₃, hk₃, h5, gn₃, gm₃, gr₃, grm₃, go₃⟩ := inc c₂ e₂.wb_right
      (by rw [gn₂ _ (by omega), q1 _ (by omega) (by omega), r5])
      (by rw [gn₂ _ (by omega), q1 _ (by omega) (by omega), r4])
    have t : c₁.nreg 6250 < c₁.nreg 6246 := by
      rw [g6, q1 _ (by omega) (by omega), r0]; exact hs
    refine ⟨c₃, k₁ + (k₂ + 1 + k₃), .seq e₁ (.seq (.ifLtN_true t e₂) e₃), by omega, h5,
      by rw [gm₃, gm₂, iteT hs], fun x hx => ?_, by rw [gr₃, gr₂, gr₁],
      by rw [grm₃, grm₂, grm₁], by rw [go₃, go₂, go₁]⟩
    rw [gn₃ x (by omega), gn₂ x (by omega), q1 x (by omega) (by omega)]
  · obtain ⟨c₃, k₃, e₃, hk₃, h5, gn₃, gm₃, gr₃, grm₃, go₃⟩ := inc c₁ hw₁
      (by rw [q1 _ (by omega) (by omega), r5]) (by rw [q1 _ (by omega) (by omega), r4])
    have t : ¬ c₁.nreg 6250 < c₁.nreg 6246 := by
      rw [g6, q1 _ (by omega) (by omega), r0]; exact hs
    refine ⟨c₃, k₁ + (0 + 2 + k₃), .seq e₁ (.seq (.ifLtN_false t (.skip hw₁)) e₃), by omega,
      h5, by rw [gm₃, gm₁, iteF hs], fun x hx => ?_, by rw [gr₃, gr₁], by rw [grm₃, grm₁],
      by rw [go₃, go₁]⟩
    rw [gn₃ x (by omega), q1 x (by omega) (by omega)]

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- **The deletion loop**: from arrays representing `ret G R` (indices of `R` below `m`, `e`
injective there), with the flags `DF` in a third region and every flagged index an element of
`R`, within `14 m + 5` steps the arrays represent `ret G (dset e DF R m)`; memory outside the
regions of `NX` and `PR`, registers outside `6244 … 6250`, reals and output kept. -/
theorem ldProg_exec (c : Config) (hc : WordsBounded W c) {m DFb NXb PRb : ℕ}
    (r0 : c.nreg 6240 = m) (r1 : c.nreg 6241 = DFb) (r2 : c.nreg 6242 = NXb)
    (r3 : c.nreg 6243 = PRb) (w1 : DFb + m ≤ W) (w2 : NXb + m ≤ W) (w3 : PRb + m ≤ W)
    (w4 : m + 1 ≤ W)
    (d1 : ∀ j < m, ∀ k < m, DFb + j ≠ NXb + k) (d2 : ∀ j < m, ∀ k < m, DFb + j ≠ PRb + k)
    (d3 : ∀ j < m, ∀ k < m, NXb + j ≠ PRb + k)
    {e : ℕ → α} {G : Perm α} {R : Finset α} (he : ∀ i < m, ∀ j < m, e i = e j → i = j)
    (hdel : ∀ j < m, 0 < c.nmem (DFb + j) → e j ∈ R)
    (hrep : RetRep e m G R c.nmem NXb PRb) :
    ∃ c' k, Exec P W ldProg c c' k ∧ k ≤ 14 * m + 5 ∧
      RetRep e m G (dset e (fun j => c.nmem (DFb + j)) R m) c'.nmem NXb PRb ∧
      (∀ a, ¬ (NXb ≤ a ∧ a < NXb + m) → ¬ (PRb ≤ a ∧ a < PRb + m) → c'.nmem a = c.nmem a) ∧
      (∀ x, (x < 6244 ∨ 6250 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold ldProg
  obtain ⟨c₁, k₁, e₁, hk₁, g4, g5, g0, gn₁, gm₁, gr₁, grm₁, go₁⟩ : ∃ c₁ k₁,
      Exec P W (block [.constN 6244 1, .constN 6245 0, .constN 6250 0]) c c₁ k₁ ∧ k₁ = 3 ∧
      c₁.nreg 6244 = 1 ∧ c₁.nreg 6245 = 0 ∧ c₁.nreg 6250 = 0 ∧
      (∀ x, x ≠ 6244 → x ≠ 6245 → x ≠ 6250 → c₁.nreg x = c.nreg x) ∧ c₁.nmem = c.nmem ∧
      c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    exec_block
    all_goals try ((try config_simp); omega)
    refine ⟨rfl, ?_, ?_, ?_, fun x a b d => ?_, rfl, rfl, rfl, rfl⟩
    · config_simp
    · config_simp
    · config_simp
    · config_simp; simp only [upd_apply]; split_ifs <;> omega
  have hw₁ := e₁.wb_right
  have q : ∀ x, x ≠ 6244 → x ≠ 6245 → x ≠ 6250 → c₁.nreg x = c.nreg x := gn₁
  set m₀ := c.nmem with hm₀
  set DF : ℕ → ℕ := fun j => m₀ (DFb + j) with hDF
  let J : ℕ → Config → Prop := fun i c' =>
    (∀ x, (x < 6245 ∨ 6249 < x) → c'.nreg x = c₁.nreg x) ∧
    RetRep e m G (dset e DF R i) c'.nmem NXb PRb ∧
    (∀ a, ¬ (NXb ≤ a ∧ a < NXb + m) → ¬ (PRb ≤ a ∧ a < PRb + m) → c'.nmem a = m₀ a) ∧
    c'.rreg = c₁.rreg ∧ c'.rmem = c₁.rmem ∧ c'.output = c₁.output
  obtain ⟨c₂, k₂, e₂, hk₂, hw₂, h75, j1, j2, j3, j4, j5, j6⟩ := lnRange (P := P) (a := 6245)
    (b := 6240) (body := ldBody) J (B := 12) c₁ hw₁ g5
    (by rw [q _ (by omega) (by omega) (by omega), r0]) (Nat.zero_le m)
    ⟨fun _ _ => rfl, by rw [dset_zero, gm₁]; exact hrep, fun a _ _ => by rw [gm₁],
      rfl, rfl, rfl⟩
    (fun i c' hlo hhi hw h75 h70 ⟨j1, j2, j3, j4, j5, j6⟩ => by
      have f : ∀ x, (x < 6245 ∨ 6249 < x) → c'.nreg x = c₁.nreg x := j1
      have eDF : c'.nmem (DFb + i) = DF i :=
        j3 _ (fun h => d1 i hhi (DFb + i - NXb) (by omega) (by omega))
          (fun h => d2 i hhi (DFb + i - PRb) (by omega) (by omega))
      have hiR : 0 < DF i → e i ∈ dset e DF R i := fun hp =>
        mem_dset_of (hdel i hhi hp) (fun j hj h => by have := he j (by omega) i hhi h; omega)
      obtain ⟨c'', t, ex, ht, h75', hm', hn', hr', hrm', ho'⟩ := ldBody_exec (P := P) c' hw
        (by rw [f _ (by omega), q _ (by omega) (by omega) (by omega), r1])
        (by rw [f _ (by omega), q _ (by omega) (by omega) (by omega), r2])
        (by rw [f _ (by omega), q _ (by omega) (by omega) (by omega), r3])
        (by rw [f _ (by omega), g4]) h75 (by rw [f _ (by omega), g0]) (by omega) (by omega)
        (by omega) (fun hp => by
          rw [eDF] at hp
          obtain ⟨a1, a2, -, -⟩ := j2 i hhi (hiR hp)
          exact ⟨by omega, by omega⟩) (by omega)
      rw [eDF] at hm'
      refine ⟨c'', t, ex, ht, h75', by rw [hn' _ (by omega)]; exact h70,
        fun x hx => by rw [hn' x hx, f x hx], ?_, fun a ha1 ha2 => ?_,
        by rw [hr', j4], by rw [hrm', j5], by rw [ho', j6]⟩
      · rw [dset_succ]
        by_cases hp : 0 < DF i
        · rw [iteT hp]
          rw [iteT hp] at hm'
          obtain ⟨a1, a2, -, -⟩ := j2 i hhi (hiR hp)
          refine retRep_erase he j2 hhi (hiR hp) (fun j hj => ?_) (fun j hj => ?_)
          · rw [hm', upd_other _ _ _ (fun h => d3 j hj _ a1 h)]
            by_cases hjp : j = c'.nmem (PRb + i)
            · rw [iteT hjp, hjp, upd_same]
            · rw [iteF hjp, upd_other _ _ _ (by omega)]
          · rw [hm']
            by_cases hjs : j = c'.nmem (NXb + i)
            · rw [iteT hjs, hjs, upd_same]
            · rw [iteF hjs, upd_other _ _ _ (by omega),
                upd_other _ _ _ (fun h => d3 _ a2 j hj h.symm)]
        · rw [iteF hp]; rw [iteF hp] at hm'; rw [hm']; exact j2
      · rw [hm']
        split_ifs with hp
        · obtain ⟨a1, a2, -, -⟩ := j2 i hhi (hiR hp)
          rw [upd_other _ _ _ (fun h => ha2 ⟨by omega, by omega⟩),
            upd_other _ _ _ (fun h => ha1 ⟨by omega, by omega⟩)]
          exact j3 a ha1 ha2
        · exact j3 a ha1 ha2)
  refine ⟨c₂, k₁ + k₂, .seq e₁ e₂, by omega, j2, j3, fun x hx => ?_, by rw [j4, gr₁],
    by rw [j5, grm₁], by rw [j6, go₁]⟩
  rw [j1 x (by omega), q x (by omega) (by omega) (by omega)]

end Exec

end BKMNW

end PlanarFlow
