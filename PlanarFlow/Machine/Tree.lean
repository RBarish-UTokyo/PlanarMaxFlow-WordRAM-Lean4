module

public import PlanarFlow.Machine.Reach

/-!
# Feasibility on the machine: the base flow along the spanning tree

The base flow `g` starts at `0` on every dart, the excess of every vertex at its supply minus
its demand. The vertices other than the root are processed in the reverse order of discovery:
a vertex `v` with excess `x` and parent dart `i` (from its parent `p` to `v`) sets `g (rv i) = x`,
`g i = -x` and adds `x` to the excess of `p`. Every processed vertex then has net flow
`bp v - bn v` in `g`, and every other vertex `v` has excess `bp v - bn v - (net flow of g out
of v)`; at the end the excess left at the root is the total of the supplies minus the demands
(`tree_exec`). The root check sets `r32 = 1` exactly when it is `0`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace Feas

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs Finset

variable {d : List ℕ} {W : ℕ}

/-! ### Pure lemmas -/

lemma hd_rv (he : Enc d W) {i : ℕ} (hi : i < nd d) : hd d (rv d i) = tl d i := by
  unfold hd; rw [he.wf.rv_rv i hi]

/-- The net flow after changing a function on two darts where it vanished. -/
lemma dv_two (g g' : ℕ → ℤ) {i j : ℕ} (hi : i < nd d) (hj : j < nd d) (hij : i ≠ j)
    (hgi : g i = 0) (hgj : g j = 0) (α β : ℤ)
    (hg' : ∀ l < nd d, g' l = if l = i then α else if l = j then β else g l) (w : ℕ) :
    dv d g' w = dv d g w + (if tl d i = w then α else 0) + (if tl d j = w then β else 0) := by
  have h : ∀ l ∈ (range (nd d)).filter (fun l => tl d l = w),
      g' l = g l + (if l = i then α else 0) + (if l = j then β else 0) := by
    intro l hl
    rw [hg' l (mem_range.1 (mem_filter.1 hl).1)]
    by_cases h1 : l = i
    · subst h1; simp [hij, hgi]
    · by_cases h2 : l = j
      · subst h2; simp [h1, hgj]
      · simp [h1, h2]
  unfold dv
  rw [sum_congr rfl h, sum_add_distrib, sum_add_distrib, sum_ite_eq', sum_ite_eq']
  simp [hi, hj]

/-- The net flows of an antisymmetric function add up to zero. -/
lemma sum_dv (he : Enc d W) {g : ℕ → ℤ} (hg : ∀ j < nd d, g (rv d j) = - g j) :
    ∑ v ∈ range (nv d), dv d g v = 0 := by
  have h1 : ∑ v ∈ range (nv d), dv d g v = ∑ j ∈ range (nd d), g j := by
    unfold dv
    exact sum_fiberwise_of_maps_to (fun j hj => mem_range.2 (he.wf.tl_lt j (mem_range.1 hj))) g
  have h2 : ∑ j ∈ range (nd d), g j = ∑ j ∈ range (nd d), g (rv d j) := by
    refine sum_nbij' (rv d) (rv d) (fun j hj => mem_range.2 (he.wf.rv_lt j (mem_range.1 hj)))
      (fun j hj => mem_range.2 (he.wf.rv_lt j (mem_range.1 hj)))
      (fun j hj => he.wf.rv_rv j (mem_range.1 hj)) (fun j hj => he.wf.rv_rv j (mem_range.1 hj))
      (fun j hj => by rw [he.wf.rv_rv j (mem_range.1 hj)])
  have h3 : ∑ j ∈ range (nd d), g (rv d j) = - ∑ j ∈ range (nd d), g j := by
    rw [← sum_neg_distrib]; exact sum_congr rfl fun j hj => hg j (mem_range.1 hj)
  rw [h1]; linarith

/-- The parent darts of two vertices discovered at positions `k' ≥ r > k` and `k` are different
edges. -/
lemma par_ne (he : Enc d W) {m : ℕ → ℕ} (h : RS d (nv d) m) {k k' : ℕ} (hk : 1 ≤ k)
    (hkk' : k < k') (hk' : k' < nv d) :
    pr d m (od d m k) ≠ pr d m (od d m k') ∧ pr d m (od d m k) ≠ rv d (pr d m (od d m k')) ∧
    rv d (pr d m (od d m k)) ≠ pr d m (od d m k') ∧
    rv d (pr d m (od d m k)) ≠ rv d (pr d m (od d m k')) := by
  obtain ⟨hi, hhi, kp, hkp, htp⟩ := h.par k hk (by omega)
  obtain ⟨hi', hhi', kp', hkp', htp'⟩ := h.par k' (by omega) hk'
  generalize hI : pr d m (od d m k) = i at *
  generalize hI' : pr d m (od d m k') = i' at *
  have hinj := h.od_inj
  have e1 : i ≠ i' := by
    rintro rfl
    have := hinj k (by omega) k' hk' (hhi.symm.trans hhi'); omega
  have e2 : i ≠ rv d i' := by
    rintro rfl
    -- the tail of `rv i'` is the head of `i'`
    have h1 : tl d (rv d i') = od d m k' := hhi'
    rw [h1] at htp
    have := hinj kp (by omega) k' hk' htp.symm; omega
  refine ⟨e1, e2, fun e => e2 (by rw [← e, he.wf.rv_rv i hi]), fun e => e1 ?_⟩
  have := congrArg (rv d) e
  rwa [he.wf.rv_rv i hi, he.wf.rv_rv i' hi'] at this

/-! ### Initialization of the base flow and of the excesses -/

/-- The state of the initialization of the base flow, from the memory `m₀`. -/
structure IG (d : List ℕ) (W : ℕ) (m₀ : ℕ → ℕ) (c : Config) : Prop where
  wb : WordsBounded W c
  regs : Regs d c
  out : c.output = []
  r20 : c.nreg 20 ≤ nd d
  done : ∀ j < c.nreg 20, c.nmem j = zz d
  frame : ∀ a, nd d ≤ a → c.nmem a = m₀ a

theorem gStep_exec (he : Enc d W) {m₀ : ℕ → ℕ} (c : Config) (hI : IG d W m₀ c)
    (hlt : c.nreg 20 < c.nreg 4) :
    ∃ c' k, Exec (inp d) W gStep c c' k ∧ IG d W m₀ c' ∧
      (nd d - c'.nreg 20) * 4 + k + 2 ≤ (nd d - c.nreg 20) * 4 := by
  have hc := hI.wb
  have hs := he.size
  obtain ⟨⟨h0, h1, h2, h3, h4, h5, h7, h8, h9, h10, h11, h12, h13⟩, h6⟩ := hI.regs
  rw [h4] at hlt
  unfold gStep
  exec_block
  · config_simp; rw [h1]; omega
  refine ⟨⟨‹_›, regs_of hI.regs fun r hr => by config_simp; rw [upd_other _ _ _ (by omega)],
    by config_simp; exact hI.out, by config_simp; rw [h1]; omega, fun j hj => ?_, fun a ha => ?_⟩,
    by config_simp; rw [h1]; omega⟩
  · config_simp at hj; rw [h1] at hj; config_simp
    rw [upd_apply]; split_ifs with h
    · exact h6
    · exact hI.done j (by omega)
  · config_simp; rw [upd_other _ _ _ (by omega)]; exact hI.frame a ha

/-- The state of the initialization of the excesses, from the memory `m₁`. -/
structure IX (d : List ℕ) (W : ℕ) (m₁ : ℕ → ℕ) (c : Config) : Prop where
  wb : WordsBounded W c
  regs : Regs d c
  out : c.output = []
  r20 : c.nreg 20 ≤ nv d
  done : ∀ v < c.nreg 20, c.nmem (nd d + 3 * nv d + v) = zz d + bp d v - bn d v
  frame : ∀ a, a < nd d + 3 * nv d → c.nmem a = m₁ a

theorem exStep_exec (he : Enc d W) {m₁ : ℕ → ℕ} (c : Config) (hI : IX d W m₁ c)
    (hlt : c.nreg 20 < c.nreg 2) :
    ∃ c' k, Exec (inp d) W exStep c c' k ∧ IX d W m₁ c' ∧
      (nv d - c'.nreg 20) * 12 + k + 2 ≤ (nv d - c.nreg 20) * 12 := by
  have hc := hI.wb
  have hs := he.size
  have hb := he.big
  obtain ⟨⟨h0, h1, h2, h3, h4, h5, h7, h8, h9, h10, h11, h12, h13⟩, h6⟩ := hI.regs
  rw [h2] at hlt
  have hle := bp_le_bsum (d := d) hlt
  have e1 : word d (c.nreg 20 * 2 + (nd d * 5 + 3)) = bp d (c.nreg 20) := rfl
  have e2 : word d (c.nreg 20 * 2 + (nd d * 5 + 3) + 1) = bn d (c.nreg 20) := rfl
  unfold exStep
  exec_block
  · config_simp; rw [h12]; omega
  · config_simp; rw [h12, h11]; omega
  · config_simp; exact he.word_le _
  · config_simp; rw [h12, h11, h1]; omega
  · config_simp; exact he.word_le _
  · config_simp; rw [h6, word_inp, h12, h11, e1]; omega
  · config_simp; rw [h9]; omega
  · config_simp; rw [h1]; omega
  simp only [word_inp, h12, h11, h1, h6, h9, e1, e2] at *
  obtain ⟨⟨h0, h1, h2, h3, h4, h5, h7, h8, h9, h10, h11, h12, h13⟩, h6⟩ := hI.regs
  refine ⟨⟨‹_›, regs_of hI.regs fun r hr => by
      config_simp; simp only [upd_apply]; split_ifs <;> first | rfl | omega,
    by config_simp; exact hI.out, by config_simp; omega, fun v hv => ?_, fun a ha => ?_⟩,
    by config_simp; omega⟩
  · config_simp at hv; config_simp
    rw [upd_apply]; split_ifs with h
    · have : v = c.nreg 20 := by omega
      subst this; omega
    · exact hI.done v (by omega)
  · config_simp; rw [upd_other _ _ _ (by omega)]; exact hI.frame a ha

/-! ### The tree -/

/-- The state of the base-flow phase; `m₁` is the memory after the search, `r29` the number of
vertices not yet processed. -/
structure IT (d : List ℕ) (W : ℕ) (m₁ : ℕ → ℕ) (c : Config) : Prop where
  wb : WordsBounded W c
  regs : Regs d c
  out : c.output = []
  r29_pos : 1 ≤ c.nreg 29
  r29_le : c.nreg 29 ≤ nv d
  tree : ∀ a, nd d ≤ a → a < nd d + 3 * nv d → c.nmem a = m₁ a
  anti : ∀ j < nd d, sv d c.nmem (rv d j) = - sv d c.nmem j
  done : ∀ k, c.nreg 29 ≤ k → k < nv d → dv d (sv d c.nmem) (od d m₁ k) = bb d (od d m₁ k)
  todo : ∀ k < c.nreg 29, exv d c.nmem (od d m₁ k) = bb d (od d m₁ k) - dv d (sv d c.nmem) (od d m₁ k)
  supp : ∀ j < nd d, sv d c.nmem j ≠ 0 → ∃ k, c.nreg 29 ≤ k ∧ k < nv d ∧
    (j = pr d m₁ (od d m₁ k) ∨ j = rv d (pr d m₁ (od d m₁ k)))
  gbd : ∀ j < nd d, |sv d c.nmem j| ≤ bsum d
  exsum : ∑ k ∈ range (c.nreg 29), |exv d c.nmem (od d m₁ k)| ≤ bsum d

/-- One vertex of the tree, on the memory. -/
theorem IT.step (he : Enc d W) {m₁ : ℕ → ℕ} (hT : RS d (nv d) m₁) {c c' : Config}
    (hI : IT d W m₁ c) (hlt : 1 < c.nreg 29) (hw : WordsBounded W c') (hR : Regs d c')
    (hout : c'.output = c.output) (h29 : c'.nreg 29 = c.nreg 29 - 1)
    (hmem : c'.nmem = upd (upd (upd c.nmem (rv d (pr d m₁ (od d m₁ (c.nreg 29 - 1))))
        (c.nmem (nd d + 3 * nv d + od d m₁ (c.nreg 29 - 1))))
      (pr d m₁ (od d m₁ (c.nreg 29 - 1)))
        (zz d + zz d - c.nmem (nd d + 3 * nv d + od d m₁ (c.nreg 29 - 1))))
      (nd d + 3 * nv d + tl d (pr d m₁ (od d m₁ (c.nreg 29 - 1))))
        (c.nmem (nd d + 3 * nv d + tl d (pr d m₁ (od d m₁ (c.nreg 29 - 1)))) +
          c.nmem (nd d + 3 * nv d + od d m₁ (c.nreg 29 - 1)) - zz d)) :
    IT d W m₁ c' := by
  have hzb := zz_ge d
  have hr := hI.r29_le
  generalize hk : c.nreg 29 - 1 = k at hmem h29
  have hk1 : 1 ≤ k := by omega
  have hknv : k < nv d := by omega
  have hr29 : c.nreg 29 = k + 1 := by omega
  generalize hv : od d m₁ k = v at hmem
  have hvn : v < nv d := hv ▸ hT.od_lt k hknv
  obtain ⟨hi, hhi, kp, hkp, htp⟩ := hT.par k hk1 hknv
  rw [hv] at hi hhi htp
  generalize hI' : pr d m₁ v = i at hi hhi htp hmem
  generalize hp : tl d i = p at htp hmem
  have hpn : p < nv d := hp ▸ he.wf.tl_lt i hi
  have hj := he.wf.rv_lt i hi
  have hij : i ≠ rv d i := (he.wf.rv_ne i hi).symm
  have hpv : p ≠ v := fun e => by
    have := hT.od_inj kp (by omega) k hknv (htp.symm.trans (e.trans hv.symm)); omega
  have hodp : od d m₁ kp = p := htp.symm
  -- the excesses of `v` and `p`
  generalize hx : exv d c.nmem v = x
  generalize hy : exv d c.nmem p = y
  have hxy : |y| + |x| ≤ bsum d := by
    have h := hI.exsum
    rw [hr29, sum_range_succ, hv, hx] at h
    have h2 : |y| ≤ ∑ k' ∈ range k, |exv d c.nmem (od d m₁ k')| := by
      rw [← hy, ← hodp]
      exact single_le_sum (f := fun k' => |exv d c.nmem (od d m₁ k')|)
        (fun _ _ => abs_nonneg _) (mem_range.2 hkp)
    linarith
  have hX : (c.nmem (nd d + 3 * nv d + v) : ℤ) = x + zz d := by
    rw [← hx]; unfold exv sv; ring
  have hY : (c.nmem (nd d + 3 * nv d + p) : ℤ) = y + zz d := by
    rw [← hy]; unfold exv sv; ring
  have hxa := abs_le.1 (show |x| ≤ bsum d by linarith [abs_nonneg y])
  have hya := abs_le.1 (show |y| ≤ bsum d by linarith [abs_nonneg x])
  -- the new values
  have hxa' := neg_abs_le x
  have hya' := neg_abs_le y
  have hsv : ∀ l < nd d, sv d c'.nmem l = if l = i then -x else if l = rv d i then x
      else sv d c.nmem l := by
    intro l hl
    unfold sv
    rw [hmem, upd_other _ _ _ (by omega)]
    by_cases h1 : l = i
    · subst h1; rw [upd_same, Nat.cast_sub (by omega)]; push_cast; rw [hX]; simp
    · rw [upd_other _ _ _ h1]
      by_cases h2 : l = rv d i
      · subst h2; rw [upd_same, hX]; simp [h1]
      · rw [upd_other _ _ _ h2]; simp [h1, h2]
  have hex : ∀ w < nv d, exv d c'.nmem w = if w = p then y + x else exv d c.nmem w := by
    intro w hw
    unfold exv sv
    by_cases h1 : w = p
    · subst h1; rw [hmem, upd_same, Nat.cast_sub (by omega)]; push_cast; rw [hX, hY]; simp; ring
    · rw [hmem, upd_other _ _ _ (by omega), upd_other _ _ _ (by omega),
        upd_other _ _ _ (by omega)]
      simp [h1]
  -- the parent dart was not used yet
  have hold : ∀ l, (l = i ∨ l = rv d i) → sv d c.nmem l = 0 := by
    intro l hl
    by_contra hne
    obtain ⟨k', hk', hk'n, hk'e⟩ := hI.supp l (by rcases hl with rfl | rfl <;> omega) hne
    have hne' := par_ne he hT hk1 (show k < k' by omega) hk'n
    rw [hv, hI'] at hne'
    rcases hl with rfl | rfl <;> rcases hk'e with e | e
    · exact hne'.1 e
    · exact hne'.2.1 e
    · exact hne'.2.2.1 e
    · exact hne'.2.2.2 e
  have hdv : ∀ w, dv d (sv d c'.nmem) w = dv d (sv d c.nmem) w + (if p = w then -x else 0) +
      (if v = w then x else 0) := by
    intro w
    have := dv_two (d := d) (sv d c.nmem) (sv d c'.nmem) hi hj hij (hold i (Or.inl rfl))
      (hold (rv d i) (Or.inr rfl)) (-x) x hsv w
    rw [this, hp, ← hhi]
    rfl
  have hfr : ∀ a, nd d ≤ a → a < nd d + 3 * nv d → c'.nmem a = c.nmem a := by
    intro a ha1 ha2
    rw [hmem, upd_other _ _ _ (by omega), upd_other _ _ _ (by omega), upd_other _ _ _ (by omega)]
  refine ⟨hw, hR, hout.trans hI.out, by omega, by omega, fun a ha1 ha2 => ?_, fun l hl => ?_,
    fun k' hk' hk'n => ?_, fun k' hk' => ?_, fun l hl hne => ?_, fun l hl => ?_, ?_⟩
  · rw [hfr a ha1 ha2]; exact hI.tree a ha1 ha2
  · have hrl := he.wf.rv_lt l hl
    rw [hsv _ hrl, hsv _ hl]
    by_cases h1 : l = i
    · have h' : rv d i ≠ i := he.wf.rv_ne i hi
      simp [h1, h']
    · by_cases h2 : l = rv d i
      · subst h2; simp [he.wf.rv_rv i hi, h1]
      · have h3 : rv d l ≠ i := fun e => h2 (by rw [← e, he.wf.rv_rv l hl])
        have h4 : rv d l ≠ rv d i := fun e => h1 (by
          have := congrArg (rv d) e; rwa [he.wf.rv_rv l hl, he.wf.rv_rv i hi] at this)
        simp only [h1, h2, h3, h4, ite_false]
        exact hI.anti l hl
  · rw [h29] at hk'
    rw [hdv]
    rcases Nat.lt_or_ge k k' with hlt' | hle'
    · have h1 : p ≠ od d m₁ k' := fun e => by
        have := hT.od_inj kp (by omega) k' hk'n (hodp.trans e); omega
      have h2 : v ≠ od d m₁ k' := fun e => by
        have := hT.od_inj k hknv k' hk'n (hv.trans e); omega
      simp only [h1, h2, ite_false, add_zero]
      exact hI.done k' (by omega) hk'n
    · have hkk : k' = k := by omega
      rw [hkk, hv]
      simp only [hpv, ite_false, ite_true, add_zero]
      have := hI.todo k (by omega)
      rw [hv, hx] at this
      linarith
  · rw [h29] at hk'
    have hw := hT.od_lt k' (by omega)
    rw [hex _ hw, hdv]
    have h2 : v ≠ od d m₁ k' := fun e => by
      have := hT.od_inj k hknv k' (by omega) (hv.trans e); omega
    simp only [h2, ite_false, add_zero]
    have := hI.todo k' (by omega)
    by_cases h1 : od d m₁ k' = p
    · rw [h1] at this ⊢; rw [hy] at this; simp only [ite_true]; linarith
    · simp only [h1, Ne.symm h1, ite_false, add_zero]; exact this
  · rw [h29]
    rw [hsv l hl] at hne
    by_cases h1 : l = i
    · exact ⟨k, by omega, hknv, Or.inl (by rw [h1, hv, hI'])⟩
    · by_cases h2 : l = rv d i
      · exact ⟨k, by omega, hknv, Or.inr (by rw [h2, hv, hI'])⟩
      · simp only [h1, h2, ite_false] at hne
        obtain ⟨k', hk', hk'n, e⟩ := hI.supp l hl hne
        exact ⟨k', by omega, hk'n, e⟩
  · rw [hsv l hl]
    split_ifs
    · rw [abs_neg]; linarith [abs_nonneg y]
    · linarith [abs_nonneg y]
    · exact hI.gbd l hl
  · rw [h29]
    have h := hI.exsum
    rw [hr29, sum_range_succ, hv, hx] at h
    have hle : ∀ k' ∈ range k, |exv d c'.nmem (od d m₁ k')| ≤
        |exv d c.nmem (od d m₁ k')| + (if k' = kp then |x| else 0) := by
      intro k' hk'
      have hk'k := mem_range.1 hk'
      rw [hex _ (hT.od_lt k' (by omega))]
      by_cases h1 : od d m₁ k' = p
      · have : k' = kp := hT.od_inj k' (by omega) kp (by omega) (h1.trans hodp.symm)
        subst this
        simp only [h1, ite_true, hy]
        exact abs_add_le y x
      · have : k' ≠ kp := fun e => h1 (e ▸ hodp)
        simp [h1, this]
    have := sum_le_sum hle
    rw [sum_add_distrib, sum_ite_eq'] at this
    simp only [mem_range, hkp, ite_true] at this
    linarith

theorem treeStep_exec (he : Enc d W) {m₁ : ℕ → ℕ} (hT : RS d (nv d) m₁) (c : Config)
    (hI : IT d W m₁ c) (hlt : c.nreg 1 < c.nreg 29) :
    ∃ c' k, Exec (inp d) W treeStep c c' k ∧ IT d W m₁ c' ∧
      c'.nreg 29 * 23 + k + 2 ≤ c.nreg 29 * 23 := by
  have hc := hI.wb
  have hs := he.size
  have hb := he.big
  have hzb := zz_ge d
  obtain ⟨⟨h0, h1, h2, h3, h4, h5, h7, h8, h9, h10, h11, h12, h13⟩, h6⟩ := hI.regs
  rw [h1] at hlt
  have hr := hI.r29_le
  generalize hk : c.nreg 29 - 1 = k
  have hk' : c.nreg 29 - c.nreg 1 = k := by rw [h1]; exact hk
  have hk1 : 1 ≤ k := by omega
  have hknv : k < nv d := by omega
  -- the vertex, its parent dart, its parent
  generalize hv : od d m₁ k = v
  have hvn : v < nv d := hv ▸ hT.od_lt k hknv
  obtain ⟨hi, hhi, kp, hkp, htp⟩ := hT.par k hk1 hknv
  rw [hv] at hi hhi htp
  generalize hI' : pr d m₁ v = i at hi hhi htp
  generalize hp : tl d i = p at htp
  have hpn : p < nv d := hp ▸ he.wf.tl_lt i hi
  have hj := he.wf.rv_lt i hi
  have hij : i ≠ rv d i := (he.wf.rv_ne i hi).symm
  have hpv : p ≠ v := fun e => by
    have := hT.od_inj kp (by omega) k hknv (htp.symm.trans (e.trans hv.symm)); omega
  -- memory readings
  have hmv : c.nmem (nd d + 2 * nv d + k) = v := by
    rw [hI.tree _ (by omega) (by omega)]; exact hv
  have hmi : c.nmem (nd d + nv d + v) = i := by
    rw [hI.tree _ (by omega) (by omega)]; exact hI'
  generalize hx : exv d c.nmem v = x
  have hxsum : |x| ≤ bsum d := by
    have := hI.exsum
    rw [show c.nreg 29 = k + 1 by omega, sum_range_succ, hv, hx] at this
    have := sum_nonneg (fun k' (_ : k' ∈ range k) => abs_nonneg (exv d c.nmem (od d m₁ k')))
    linarith
  have hX : (c.nmem (nd d + 3 * nv d + v) : ℤ) = x + zz d := by
    rw [← hx]; unfold exv sv; ring
  have hXn : c.nmem (nd d + 3 * nv d + v) ≤ zz d + bsum d := by
    have := abs_le.1 hxsum; omega
  have hXz : zz d ≤ c.nmem (nd d + 3 * nv d + v) + bsum d := by
    have := abs_le.1 hxsum; omega
  generalize hy : exv d c.nmem p = y
  have hpk : ∃ k', k' < k ∧ od d m₁ k' = p := ⟨kp, hkp, htp.symm⟩
  have hysum : |y| ≤ bsum d := by
    have h := hI.exsum
    rw [show c.nreg 29 = k + 1 by omega, sum_range_succ] at h
    have h2 : |y| ≤ ∑ k' ∈ range k, |exv d c.nmem (od d m₁ k')| := by
      rw [← hy, htp]
      exact single_le_sum (f := fun k' => |exv d c.nmem (od d m₁ k')|)
        (fun _ _ => abs_nonneg _) (mem_range.2 hkp)
    have := abs_nonneg (exv d c.nmem (od d m₁ k))
    linarith
  have hY : (c.nmem (nd d + 3 * nv d + p) : ℤ) = y + zz d := by
    rw [← hy]; unfold exv sv; ring
  have e1 : word d (i * 5 + 3) = p := hp
  have e2 : word d (i * 5 + 3 + 1) = rv d i := rfl
  have hw1 := he.word_le (i * 5 + 3)
  have hw2 := he.word_le (i * 5 + 3 + 1)
  unfold treeStep
  exec_block
  · config_simp; rw [h8]; omega
  · config_simp; rw [h8, hk', hmv, h7]; omega
  · config_simp; rw [h8, hk', hmv, h9]; omega
  · config_simp; rw [h8, hk', hmv, h7, hmi, h5]; omega
  · config_simp; rw [h8, hk', hmv, h7, hmi, h5, h13]; omega
  · config_simp; exact he.word_le _
  · config_simp; rw [h8, hk', hmv, h7, hmi, h5, h13, h1]; omega
  · config_simp; exact he.word_le _
  · config_simp; rw [h6]; omega
  · config_simp; rw [h8, hk', hmv, h7, hmi, h5, h13, h9, word_inp, e1]; omega
  · config_simp
    rw [h8, hk', hmv, h7, hmi, h5, h13, h9, h1, word_inp, word_inp, e1, e2, h6]
    simp only [upd_apply]
    split_ifs <;> first | omega | (have := abs_le.1 hysum; omega)
  have ha1 : nd d + 3 * nv d + p ≠ i := by omega
  have ha2 : nd d + 3 * nv d + p ≠ rv d i := by have := he.wf.rv_lt i hi; omega
  refine ⟨IT.step he hT hI hlt ‹_› (regs_of hI.regs fun r hr => by
      config_simp; simp only [upd_apply]; split_ifs <;> first | rfl | omega)
    (by config_simp) (by config_simp; rw [h1]) ?_, by config_simp; rw [h1]; omega⟩
  config_simp
  simp only [h1, h5, h6, h7, h8, h9, h13, hk', hk, hmv, hmi, word_inp, e1, e2, hv, hI', hp]
  rw [upd_other _ _ _ ha1, upd_other _ _ _ ha2]

/-! ### The loops of the phase -/

theorem gloop_exec (he : Enc d W) (c : Config) (hc : WordsBounded W c) (hR : Regs d c)
    (ho : c.output = []) (h20 : c.nreg 20 = 0) :
    ∃ c' k, Exec (inp d) W (.whileLtN 20 4 gStep) c c' k ∧ WordsBounded W c' ∧ Regs d c' ∧
      c'.output = [] ∧ (∀ j < nd d, c'.nmem j = zz d) ∧ (∀ a, nd d ≤ a → c'.nmem a = c.nmem a) ∧
      k ≤ 4 * nd d + 2 := by
  obtain ⟨c', k, e, hI, hn, hk⟩ := Exec.whileLtN_potential (P := inp d) (W := W) (a := 20)
    (b := 4) (body := gStep) (IG d W c.nmem) (fun c => (nd d - c.nreg 20) * 4) (fun c h => h.wb)
    (fun c hc hlt => gStep_exec he c hc hlt)
    ⟨hc, hR, ho, by omega, fun j hj => by omega, fun a _ => rfl⟩
  have h20' : c'.nreg 20 = nd d := by have := hI.r20; rw [hI.regs.1.2.2.2.2.1] at hn; omega
  refine ⟨c', k, e, hI.wb, hI.regs, hI.out, fun j hj => hI.done j (by omega), hI.frame, ?_⟩
  beta_reduce at hk; rw [h20] at hk; omega

theorem xloop_exec (he : Enc d W) (c : Config) (hc : WordsBounded W c) (hR : Regs d c)
    (ho : c.output = []) (h20 : c.nreg 20 = 0) :
    ∃ c' k, Exec (inp d) W (.whileLtN 20 2 exStep) c c' k ∧ WordsBounded W c' ∧ Regs d c' ∧
      c'.output = [] ∧
      (∀ v < nv d, c'.nmem (nd d + 3 * nv d + v) = zz d + bp d v - bn d v) ∧
      (∀ a, a < nd d + 3 * nv d → c'.nmem a = c.nmem a) ∧ k ≤ 12 * nv d + 2 := by
  obtain ⟨c', k, e, hI, hn, hk⟩ := Exec.whileLtN_potential (P := inp d) (W := W) (a := 20)
    (b := 2) (body := exStep) (IX d W c.nmem) (fun c => (nv d - c.nreg 20) * 12)
    (fun c h => h.wb) (fun c hc hlt => exStep_exec he c hc hlt)
    ⟨hc, hR, ho, by omega, fun v hv => by omega, fun a _ => rfl⟩
  have h20' : c'.nreg 20 = nv d := by have := hI.r20; rw [hI.regs.1.2.2.1] at hn; omega
  refine ⟨c', k, e, hI.wb, hI.regs, hI.out, fun v hv => hI.done v (by omega), hI.frame, ?_⟩
  beta_reduce at hk; rw [h20] at hk; omega

/-- The start of the tree phase. -/
theorem IT.start (he : Enc d W) {m₁ : ℕ → ℕ} (hT : RS d (nv d) m₁) {c : Config}
    (hc : WordsBounded W c) (hR : Regs d c) (ho : c.output = []) (h29 : c.nreg 29 = nv d)
    (htree : ∀ a, nd d ≤ a → a < nd d + 3 * nv d → c.nmem a = m₁ a)
    (hg : ∀ j < nd d, c.nmem j = zz d)
    (hx : ∀ v < nv d, c.nmem (nd d + 3 * nv d + v) = zz d + bp d v - bn d v) :
    IT d W m₁ c := by
  have hzb := zz_ge d
  have hsv : ∀ j < nd d, sv d c.nmem j = 0 := fun j hj => by simp [sv, hg j hj]
  have hdv : ∀ v, dv d (sv d c.nmem) v = 0 := fun v =>
    sum_eq_zero fun j hj => hsv j (mem_range.1 (mem_filter.1 hj).1)
  have hex : ∀ v < nv d, exv d c.nmem v = bb d v := by
    intro v hv
    have := bp_le_bsum (d := d) hv
    unfold exv sv bb
    rw [hx v hv, Nat.cast_sub (by omega)]
    push_cast; ring
  refine ⟨hc, hR, ho, by rw [h29]; exact nv_pos he, by omega, htree,
    fun j hj => by rw [hsv j hj, hsv _ (he.wf.rv_lt j hj)]; simp, fun k hk hk' => by omega,
    fun k hk => ?_, fun j hj hne => absurd (hsv j hj) hne,
    fun j hj => by rw [hsv j hj]; simp, ?_⟩
  · rw [h29] at hk
    rw [hex _ (hT.od_lt k hk), hdv]; simp
  · rw [h29]
    have : ∑ k ∈ range (nv d), |exv d c.nmem (od d m₁ k)| = ∑ v ∈ range (nv d), |bb d v| := by
      refine sum_nbij (od d m₁) (fun k hk => mem_range.2 (hT.od_lt k (mem_range.1 hk)))
        (fun k hk l hl e => hT.od_inj k (mem_range.1 hk) l (mem_range.1 hl) e)
        (fun v hv => by
          obtain ⟨k, hk, e⟩ := hT.surj v (mem_range.1 hv)
          exact ⟨k, mem_range.2 hk, e⟩)
        (fun k hk => by rw [hex _ (hT.od_lt k (mem_range.1 hk))])
    rw [this]
    unfold bsum
    push_cast
    refine sum_le_sum fun v _ => ?_
    unfold bb
    rw [abs_le]; constructor <;> linarith [Int.natCast_nonneg (bp d v), Int.natCast_nonneg (bn d v)]

theorem tloop_exec (he : Enc d W) {m₁ : ℕ → ℕ} (hT : RS d (nv d) m₁) (c : Config)
    (hI : IT d W m₁ c) :
    ∃ c' k, Exec (inp d) W (.whileLtN 1 29 treeStep) c c' k ∧ IT d W m₁ c' ∧ c'.nreg 29 = 1 ∧
      k ≤ 23 * nv d + 2 := by
  obtain ⟨c', k, e, hI', hn, hk⟩ := Exec.whileLtN_potential (P := inp d) (W := W) (a := 1)
    (b := 29) (body := treeStep) (IT d W m₁) (fun c => c.nreg 29 * 23) (fun c h => h.wb)
    (fun c hc hlt => treeStep_exec he hT c hc hlt) hI
  have h1 := hI'.regs.1.2.1
  refine ⟨c', k, e, hI', by have := hI'.r29_pos; rw [h1] at hn; omega, ?_⟩
  have := hI.r29_le
  beta_reduce at hk; nlinarith

/-- At the end of the tree phase: every vertex but the root has the right net flow, and the
excess at the root is the total of the supplies minus the demands. -/
theorem IT.result (he : Enc d W) {m₁ : ℕ → ℕ} (hT : RS d (nv d) m₁) {c : Config}
    (hI : IT d W m₁ c) (h29 : c.nreg 29 = 1) :
    exv d c.nmem 0 = ∑ v ∈ range (nv d), bb d v ∧
      ∀ v < nv d, v ≠ 0 → dv d (sv d c.nmem) v = bb d v := by
  have hpos := nv_pos he
  have hdone : ∀ v < nv d, v ≠ 0 → dv d (sv d c.nmem) v = bb d v := by
    intro v hv hv0
    obtain ⟨k, hk, rfl⟩ := hT.surj v hv
    have hk1 : 1 ≤ k := by
      by_contra h
      have : k = 0 := by omega
      subst this; exact hv0 hT.od0
    exact hI.done k (by omega) hk
  refine ⟨?_, hdone⟩
  have h0 := hI.todo 0 (by omega)
  rw [hT.od0] at h0
  have hs := sum_dv he hI.anti
  obtain ⟨n, hn⟩ : ∃ n, nv d = n + 1 := ⟨nv d - 1, by omega⟩
  rw [hn, sum_range_succ'] at hs
  rw [hn, sum_range_succ']
  have : ∑ i ∈ range n, dv d (sv d c.nmem) (i + 1) = ∑ i ∈ range n, bb d (i + 1) :=
    sum_congr rfl fun i hi => hdone (i + 1) (by have := mem_range.1 hi; omega) (by omega)
  linarith

/-- The root check: `r32 = 1` exactly when the excess at the root is `0`. -/
theorem rootCheck_exec (c : Config) (hc : WordsBounded W c) (hR : Regs d c) :
    ∃ c' k, Exec (inp d) W rootCheck c c' k ∧ WordsBounded W c' ∧ Keeps c c' ∧
      c'.nmem = c.nmem ∧ c'.output = c.output ∧
      (c'.nreg 32 = 1 ↔ exv d c.nmem 0 = 0) ∧ c'.nreg 32 ≤ 1 ∧ k ≤ 7 := by
  obtain ⟨⟨h0, h1, h2, h3, h4, h5, h7, h8, h9, h10, h11, h12, h13⟩, h6⟩ := hR
  have hK : ∀ c' : Config, (∀ r, r ≠ 23 → r ≠ 32 → c'.nreg r = c.nreg r) → Keeps c c' :=
    fun c' h r hr => h r (by omega) (by omega)
  have hex : exv d c.nmem 0 = (c.nmem (nd d + 3 * nv d) : ℤ) - zz d := by
    simp [exv, sv]
  unfold rootCheck
  refine spec_seq ?_
  exec_block
  refine spec_seq ?_
  rcases lt_trichotomy (c.nmem (nd d + 3 * nv d)) (zz d) with hlt | heq | hgt
  · refine spec_ifLtN_true (by config_simp; rw [h9, h6]; exact hlt) ?_
    refine spec_instr (Exec.copyN ‹_› _ _) fun hw => ?_
    refine spec_ifLtN_false (by config_simp; rw [h9, h6]; omega) ?_
    refine spec_skip ‹_› ?_
    refine ⟨hw, hK _ fun r a b => ?_, by config_simp, by config_simp, ?_, by config_simp; omega,
      by omega⟩
    · config_simp; simp only [upd_apply, a, b, ite_false]
    · config_simp; rw [h0, hex]; constructor <;> intro h <;> omega
  · refine spec_ifLtN_false (by config_simp; rw [h9, h6]; omega) ?_
    refine spec_skip ‹_› ?_
    refine spec_ifLtN_false (by config_simp; rw [h9, h6]; omega) ?_
    refine spec_skip ‹_› ?_
    refine ⟨‹_›, hK _ fun r a b => ?_, by config_simp, by config_simp, ?_, by config_simp; omega,
      by omega⟩
    · config_simp; simp only [upd_apply, a, b, ite_false]
    · config_simp; rw [h1, hex, heq]; simp
  · refine spec_ifLtN_false (by config_simp; rw [h9, h6]; omega) ?_
    refine spec_skip ‹_› ?_
    refine spec_ifLtN_true (by config_simp; rw [h9, h6]; exact hgt) ?_
    refine spec_instr (Exec.copyN ‹_› _ _) fun hw => ?_
    refine ⟨hw, hK _ fun r a b => ?_, by config_simp, by config_simp, ?_, by config_simp; omega,
      by omega⟩
    · config_simp; simp only [upd_apply, a, b, ite_false]
    · config_simp; rw [h0, hex]; constructor <;> intro h <;> omega

end Feas

end PlanarFlow
