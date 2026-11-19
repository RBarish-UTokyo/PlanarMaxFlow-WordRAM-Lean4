module

public import PlanarFlow.Machine.Setup

/-!
# Feasibility on the machine: a spanning tree

`V` passes over the darts, starting with the vertex `0` marked: a dart whose tail is marked and
whose head is not marks its head, records itself as the parent dart of the head and appends the
head to the order of discovery. A pass that finds no new vertex shows that the marked vertices
are closed under the darts, hence (the graph being connected) that every vertex is marked; so
after `V` passes all `V` vertices have been discovered (`reach_exec`), within
`(22 S + 6) V + 6` steps. The parent dart of the `k`-th vertex starts at a vertex discovered
earlier.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace Feas

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs Finset

variable {d : List ℕ} {W : ℕ}

/-- The state of the search with `n` vertices found, on the memory `m`. -/
structure RS (d : List ℕ) (n : ℕ) (m : ℕ → ℕ) : Prop where
  n_pos : 1 ≤ n
  od_lt : ∀ k < n, od d m k < nv d
  od_inj : ∀ k < n, ∀ l < n, od d m k = od d m l → k = l
  od0 : od d m 0 = 0
  mk01 : ∀ v < nv d, mark d m v = 0 ∨ mark d m v = 1
  mk_iff : ∀ v < nv d, mark d m v = 1 ↔ ∃ k < n, od d m k = v
  par : ∀ k, 1 ≤ k → k < n → pr d m (od d m k) < nd d ∧ hd d (pr d m (od d m k)) = od d m k ∧
    ∃ k' < k, tl d (pr d m (od d m k)) = od d m k'

lemma hd_lt (he : Enc d W) {i : ℕ} (hi : i < nd d) : hd d i < nv d :=
  he.wf.tl_lt _ (he.wf.rv_lt i hi)

lemma nv_pos (he : Enc d W) : 0 < nv d := by
  obtain ⟨v⟩ := he.plane.nonempty
  exact lt_of_le_of_lt (Nat.zero_le _) v.2

theorem RS.le {n : ℕ} {m : ℕ → ℕ} (h : RS d n m) : n ≤ nv d := by
  classical
  have := Finset.card_le_card_of_injOn (od d m) (s := range n) (t := range (nv d))
    (fun k hk => by simp only [coe_range, Set.mem_Iio] at hk ⊢; exact h.od_lt k hk)
    (fun k hk l hl e => h.od_inj k (by simpa using hk) l (by simpa using hl) e)
  simpa using this

theorem RS.lt {n : ℕ} {m : ℕ → ℕ} (h : RS d n m) {v : ℕ} (hv : v < nv d)
    (hnot : mark d m v = 0) : n < nv d := by
  classical
  have hn : ∀ k < n, od d m k ≠ v := fun k hk e => by
    have := (h.mk_iff v hv).2 ⟨k, hk, e⟩; omega
  have := Finset.card_le_card_of_injOn (od d m) (s := range n) (t := (range (nv d)).erase v)
    (fun k hk => by
      simp only [coe_range, Set.mem_Iio] at hk
      simp only [coe_erase, coe_range, Set.mem_sdiff, Set.mem_Iio, Set.mem_singleton_iff]
      exact ⟨h.od_lt k hk, hn k hk⟩)
    (fun k hk l hl e => h.od_inj k (by simpa using hk) l (by simpa using hl) e)
  rw [card_range, card_erase_of_mem (mem_range.2 hv), card_range] at this
  omega

theorem RS.ge {n : ℕ} {m : ℕ → ℕ} (h : RS d n m) (hall : ∀ v < nv d, mark d m v = 1) :
    nv d ≤ n := by
  classical
  have := Finset.card_le_card_of_surjOn (od d m) (s := range n) (t := range (nv d))
    (fun v hv => by
      obtain ⟨k, hk, e⟩ := (h.mk_iff v (by simpa using hv)).1 (hall v (by simpa using hv))
      exact ⟨k, by simpa using hk, e⟩)
  simpa using this

/-- With all vertices found, every vertex is found. -/
theorem RS.surj {m : ℕ → ℕ} (h : RS d (nv d) m) : ∀ v < nv d, ∃ k < nv d, od d m k = v := by
  classical
  have hsub : (range (nv d)).image (od d m) ⊆ range (nv d) := by
    intro v hv
    obtain ⟨k, hk, rfl⟩ := mem_image.1 hv
    exact mem_range.2 (h.od_lt k (mem_range.1 hk))
  have hcard : (range (nv d)).card ≤ ((range (nv d)).image (od d m)).card := by
    rw [card_image_of_injOn (fun k hk l hl e => h.od_inj k (by simpa using hk) l
      (by simpa using hl) e)]
  have heq := eq_of_subset_of_card_le hsub hcard
  intro v hv
  have : v ∈ (range (nv d)).image (od d m) := by rw [heq]; exact mem_range.2 hv
  obtain ⟨k, hk, e⟩ := mem_image.1 this
  exact ⟨k, mem_range.1 hk, e⟩

/-- A new vertex is found along the dart `i`. -/
theorem RS.enq (he : Enc d W) {n : ℕ} {m : ℕ → ℕ} (h : RS d n m) {i : ℕ} (hi : i < nd d)
    (ht : mark d m (tl d i) = 1) (hh : mark d m (hd d i) = 0) :
    RS d (n + 1) (upd (upd (upd m (nd d + hd d i) 1) (nd d + nv d + hd d i) i)
      (nd d + 2 * nv d + n) (hd d i)) := by
  have hhv := hd_lt he hi
  have htv := he.wf.tl_lt i hi
  have hn := h.lt hhv hh
  generalize hg : hd d i = v at hh hhv
  generalize hm' : upd (upd (upd m (nd d + v) 1) (nd d + nv d + v) i) (nd d + 2 * nv d + n) v = m'
  have hod : ∀ k, od d m' k = if k = n then v else od d m k := by
    intro k; rw [← hm']; simp only [od, upd_apply]; split_ifs <;> first | omega | rfl
  have hmk : ∀ x < nv d, mark d m' x = if x = v then 1 else mark d m x := by
    intro x hx; rw [← hm']; simp only [mark, upd_apply]; split_ifs <;> first | omega | rfl
  have hpr : ∀ x < nv d, pr d m' x = if x = v then i else pr d m x := by
    intro x hx; rw [← hm']; simp only [pr, upd_apply]; split_ifs <;> first | omega | rfl
  have hnot : ∀ k < n, od d m k ≠ v := fun k hk e => by
    have := (h.mk_iff v hhv).2 ⟨k, hk, e⟩; omega
  have hodlt : ∀ k < n, od d m' k = od d m k := fun k hk => by
    rw [hod]; simp [show k ≠ n by omega]
  refine ⟨by omega, fun k hk => ?_, fun k hk l hl e => ?_, ?_, fun x hx => ?_, fun x hx => ?_,
    fun k hk1 hk2 => ?_⟩
  · rw [hod]; split_ifs
    · exact hhv
    · exact h.od_lt k (by omega)
  · rw [hod, hod] at e
    split_ifs at e with h1 h2 h2
    · omega
    · exact absurd e.symm (hnot l (by omega))
    · exact absurd e (hnot k (by omega))
    · exact h.od_inj k (by omega) l (by omega) e
  · rw [hodlt 0 h.n_pos]; exact h.od0
  · rw [hmk x hx]; split_ifs
    · right; rfl
    · exact h.mk01 x hx
  · rw [hmk x hx]
    split_ifs with hxv
    · subst hxv; simp only [true_iff]; exact ⟨n, by omega, by rw [hod]; simp⟩
    · rw [h.mk_iff x hx]
      constructor
      · rintro ⟨k, hk, e⟩; exact ⟨k, by omega, by rw [hodlt k hk]; exact e⟩
      · rintro ⟨k, hk, e⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
        · exact ⟨k, hk, by rw [← hodlt k hk]; exact e⟩
        · rw [hod] at e; simp at e; exact absurd e.symm hxv
  · rcases Nat.lt_succ_iff_lt_or_eq.1 hk2 with hk2 | rfl
    · rw [hodlt k hk2, hpr _ (h.od_lt k hk2)]
      simp only [show od d m k ≠ v from hnot k hk2, ↓reduceIte]
      obtain ⟨a, b, k', hk', e⟩ := h.par k hk1 hk2
      exact ⟨a, b, k', hk', by rw [hodlt k' (by omega)]; exact e⟩
    · rw [hod]; simp only [↓reduceIte]
      rw [hpr _ hhv]; simp only [↓reduceIte]
      refine ⟨hi, hg, ?_⟩
      obtain ⟨k', hk', e⟩ := (h.mk_iff _ htv).1 ht
      exact ⟨k', hk', by rw [hodlt k' hk', e]⟩

/-- The state during a pass, which started with `n₀` vertices found. -/
structure JR (d : List ℕ) (W : ℕ) (n₀ p : ℕ) (c : Config) : Prop where
  wb : WordsBounded W c
  regs : Regs d c
  out : c.output = []
  rs : RS d (c.nreg 25) c.nmem
  r20 : c.nreg 20 ≤ nd d
  r26 : c.nreg 26 = p
  n0 : n₀ ≤ c.nreg 25
  prog : c.nreg 25 = n₀ → ∀ j < c.nreg 20, ¬ (mark d c.nmem (tl d j) = 1 ∧ mark d c.nmem (hd d j) = 0)

theorem scan_exec (he : Enc d W) {n₀ p : ℕ} (c : Config) (hJ : JR d W n₀ p c)
    (hlt : c.nreg 20 < c.nreg 4) :
    ∃ c' k, Exec (inp d) W scan c c' k ∧ JR d W n₀ p c' ∧
      (nd d - c'.nreg 20) * 22 + k + 2 ≤ (nd d - c.nreg 20) * 22 := by
  have hc := hJ.wb
  have hs := he.size
  obtain ⟨⟨h0, h1, h2, h3, h4, h5, h7, h8, h9, h10, h11, h12, h13⟩, h6⟩ := hJ.regs
  rw [h4] at hlt
  have hrv := he.wf.rv_lt _ hlt
  have htv := he.wf.tl_lt _ hlt
  have hhv := hd_lt he hlt
  have hcn := hJ.rs.le
  have e1 : word d (c.nreg 20 * 5 + 3) = tl d (c.nreg 20) := rfl
  have e2 : word d (c.nreg 20 * 5 + 3 + 1) = rv d (c.nreg 20) := rfl
  have e3 : word d (rv d (c.nreg 20) * 5 + 3) = hd d (c.nreg 20) := rfl
  have hw1 := he.word_le (c.nreg 20 * 5 + 3)
  have hw2 := he.word_le (c.nreg 20 * 5 + 3 + 1)
  have hK : ∀ c' : Config, (∀ r, r ≠ 20 → r ≠ 22 → r ≠ 23 → r ≠ 24 → r ≠ 25 → r ≠ 27 →
      r ≠ 28 → c'.nreg r = c.nreg r) → Keeps c c' := fun c' h r hr =>
    h r (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  unfold scan
  refine spec_seq ?_
  exec_block
  · config_simp; rw [h5]; omega
  · config_simp; rw [h5, h13]; omega
  · config_simp; exact he.word_le _
  · config_simp; rw [h5, h13, h1]; omega
  · config_simp; exact he.word_le _
  · config_simp; rw [h5, h13, h1, word_inp, e2]; omega
  · config_simp; rw [h5, h13, h1, word_inp, e2]; omega
  · config_simp; exact he.word_le _
  · config_simp; rw [h4, h5, h13, word_inp, e1]; omega
  · config_simp; rw [h4, h5, h13, h1, word_inp, word_inp, e2, e3]; omega
  config_simp
  simp only [h1, h4, h5, h13, word_inp, e1, e2, e3] at *
  obtain ⟨⟨h0, h1, h2, h3, h4, h5, h7, h8, h9, h10, h11, h12, h13⟩, h6⟩ := hJ.regs
  refine spec_seq ?_
  have hm1 := hJ.rs.mk01 _ htv
  have hm2 := hJ.rs.mk01 _ hhv
  by_cases hnew : mark d c.nmem (tl d (c.nreg 20)) = 1 ∧ mark d c.nmem (hd d (c.nreg 20)) = 0
  · obtain ⟨ht, hh⟩ := hnew
    have hlt' := hJ.rs.lt hhv hh
    refine spec_ifLtN_true (by config_simp; unfold mark at ht hh; omega) ?_
    exec_block
    · config_simp; rw [h7]; omega
    · config_simp; rw [h8]; omega
    · config_simp; omega
    refine spec_instr (Exec.addN ‹_› _ _ _ (by config_simp; omega)) fun hw => ?_
    have hRS := hJ.rs.enq he hlt ht hh
    refine ⟨⟨hw, regs_of hJ.regs (hK _ fun r a b e f g l m => ?_), by config_simp; exact hJ.out,
      ?_, by config_simp; omega, by config_simp; exact hJ.r26, by config_simp; have := hJ.n0; omega,
      fun hn => by config_simp at hn; have := hJ.n0; omega⟩, by config_simp; omega⟩
    · config_simp; simp only [upd_apply, a, b, e, f, g, l, m, ↓reduceIte]
    · config_simp
      simp only [h1, h4, h7, h8]
      exact hRS
  · refine spec_ifLtN_false (by
      config_simp; unfold mark at hnew hm1 hm2; omega) ?_
    refine spec_skip ‹_› ?_
    refine spec_instr (Exec.addN ‹_› _ _ _ (by config_simp; omega)) fun hw => ?_
    refine ⟨⟨hw, regs_of hJ.regs (hK _ fun r a b e f g l m => ?_), by config_simp; exact hJ.out,
      by config_simp; exact hJ.rs, by config_simp; omega, by config_simp; exact hJ.r26,
      by config_simp; exact hJ.n0, fun hn j hj => ?_⟩, by config_simp; omega⟩
    · config_simp; simp only [upd_apply, a, b, e, f, g, l, m, ↓reduceIte]
    · config_simp at hn; config_simp at hj; config_simp; rw [h1] at hj
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
      · exact hJ.prog hn j hj
      · exact hnew

/-- The marked vertices are closed under the darts: then every vertex is marked. -/
theorem all_marked (he : Enc d W) {n : ℕ} {m : ℕ → ℕ} (h : RS d n m)
    (hcl : ∀ j < nd d, ¬ (mark d m (tl d j) = 1 ∧ mark d m (hd d j) = 0)) :
    ∀ v < nv d, mark d m v = 1 := by
  intro v hv
  have h0 : mark d m 0 = 1 := (h.mk_iff 0 (nv_pos he)).2 ⟨0, h.n_pos, h.od0⟩
  have key := he.plane.conn ⟨0, nv_pos he⟩ ⟨v, hv⟩
  have : ∀ x : Fin (nv d), Relation.ReflTransGen (map he.wf).Adj ⟨0, nv_pos he⟩ x →
      mark d m x = 1 := by
    intro x hx
    induction hx with
    | refl => exact h0
    | @tail a b _ hab ih =>
      obtain ⟨j, hj1, hj2⟩ := hab
      have ht : mark d m (tl d j) = 1 := by
        have := congrArg Fin.val hj1; simp only [map] at this; rw [this]; exact ih
      have hb : b.val = hd d j := by
        have := congrArg Fin.val hj2; simp only [map, CombMap.head] at this; rw [← this]; rfl
      rw [hb]
      rcases h.mk01 _ (hd_lt he j.2) with h' | h'
      · exact absurd ⟨ht, h'⟩ (hcl j j.2)
      · exact h'
  exact this _ key

/-- The state between passes. -/
structure IR (d : List ℕ) (W : ℕ) (c : Config) : Prop where
  wb : WordsBounded W c
  regs : Regs d c
  out : c.output = []
  rs : RS d (c.nreg 25) c.nmem
  r26 : c.nreg 26 ≤ nv d
  cnt : min (nv d) (c.nreg 26 + 1) ≤ c.nreg 25

theorem pass_exec (he : Enc d W) (c : Config) (hI : IR d W c) (hlt : c.nreg 26 < c.nreg 2) :
    ∃ c' k, Exec (inp d) W pass c c' k ∧ IR d W c' ∧
      (nv d - c'.nreg 26) * (22 * nd d + 6) + k + 2 ≤ (nv d - c.nreg 26) * (22 * nd d + 6) := by
  have hc := hI.wb
  have hs := he.size
  obtain ⟨⟨h0, h1, h2, h3, h4, h5, h7, h8, h9, h10, h11, h12, h13⟩, h6⟩ := hI.regs
  rw [h2] at hlt
  have e₁ := Exec.copyN (P := inp d) hc 20 0
  have hJ : JR d W (c.nreg 25) (c.nreg 26) { c with nreg := upd c.nreg 20 (c.nreg 0) } :=
    ⟨e₁.wb_right, regs_of hI.regs fun r hr => by config_simp; rw [upd_other _ _ _ (by omega)],
      hI.out, by config_simp; exact hI.rs, by config_simp; rw [h0]; omega, by config_simp,
      by config_simp; exact le_rfl, fun _ j hj => by config_simp at hj; rw [h0] at hj; omega⟩
  obtain ⟨c₂, k₂, e₂, hJ₂, hn₂, hk₂⟩ := Exec.whileLtN_potential (P := inp d) (W := W) (a := 20)
    (b := 4) (body := scan) (JR d W (c.nreg 25) (c.nreg 26)) (fun c => (nd d - c.nreg 20) * 22)
    (fun c h => h.wb) (fun c hc hlt => scan_exec he c hc hlt) hJ
  have h20 : c₂.nreg 20 = nd d := by
    have := hJ₂.r20; rw [hJ₂.regs.1.2.2.2.2.1] at hn₂; omega
  have hw₂ := hJ₂.wb
  have h26 := hJ₂.r26
  have e₃ := Exec.addN (P := inp d) hw₂ 26 26 1 (by
    rw [h26, hJ₂.regs.1.2.1]; omega)
  refine ⟨_, _, .seq e₁ (.seq e₂ e₃), ⟨e₃.wb_right, regs_of hJ₂.regs fun r hr => by
    config_simp; rw [upd_other _ _ _ (by omega)], by config_simp; exact hJ₂.out,
    by config_simp; exact hJ₂.rs, by config_simp; rw [h26, hJ₂.regs.1.2.1]; omega, ?_⟩, ?_⟩
  · config_simp
    rw [h26, hJ₂.regs.1.2.1]
    by_cases hsame : c₂.nreg 25 = c.nreg 25
    · have hall := all_marked he hJ₂.rs (fun j hj => hJ₂.prog hsame j (by omega))
      have := hJ₂.rs.ge hall
      omega
    · have := hJ₂.n0
      have := hI.cnt
      omega
  · beta_reduce at hk₂
    config_simp
    rw [h26, hJ₂.regs.1.2.1]
    simp only [upd_same] at hk₂
    rw [h0] at hk₂
    have : (nv d - c.nreg 26) * (22 * nd d + 6) = (nv d - (c.nreg 26 + 1)) * (22 * nd d + 6) +
        (22 * nd d + 6) := by
      rw [← Nat.succ_mul]; congr 1; omega
    rw [this]
    omega

theorem reachStart_exec (he : Enc d W) (c : Config) (hc : WordsBounded W c) (hR : Regs d c)
    (hm : c.nmem = fun _ => 0) (ho : c.output = []) :
    ∃ c' k, Exec (inp d) W reachStart c c' k ∧ IR d W c' ∧ k = 4 := by
  have hs := he.size
  have hpos := nv_pos he
  obtain ⟨⟨h0, h1, h2, h3, h4, h5, h7, h8, h9, h10, h11, h12, h13⟩, h6⟩ := hR
  unfold reachStart
  exec_block
  have hmem : ∀ a, (upd (upd c.nmem (c.nreg 4) (c.nreg 1)) (c.nreg 8) (c.nreg 0)) a =
      if a = nd d then 1 else 0 := by
    intro a; simp only [upd_apply, h0, h1, h4, h8, hm]; split_ifs <;> first | omega | rfl
  have hmem' := funext hmem
  refine ⟨⟨‹_›, regs_of ⟨⟨h0, h1, h2, h3, h4, h5, h7, h8, h9, h10, h11, h12, h13⟩, h6⟩
      fun r hr => by config_simp; simp only [upd_apply]; split_ifs <;> first | rfl | omega,
    by config_simp; exact ho, ?_, by config_simp; omega, by config_simp; omega⟩, rfl⟩
  config_simp
  rw [hmem', h1]
  refine ⟨le_rfl, fun k hk => ?_, fun k hk l hl _ => by omega, ?_, fun v hv => ?_,
    fun v hv => ?_, fun k hk1 hk2 => by omega⟩
  · obtain rfl : k = 0 := by omega
    simp only [od]; split_ifs <;> omega
  · simp only [od]; split_ifs <;> omega
  · simp only [mark]; split_ifs <;> simp
  · simp only [mark, od]
    constructor
    · intro h; split_ifs at h with hv'
      · exact ⟨0, by omega, by split_ifs <;> omega⟩
    · rintro ⟨k, hk, e⟩
      obtain rfl : k = 0 := by omega
      split_ifs at e ⊢ <;> omega

/-- **The search.** After `V` passes all vertices are found. -/
theorem reach_exec (he : Enc d W) (c : Config) (hc : WordsBounded W c) (hR : Regs d c)
    (hm : c.nmem = fun _ => 0) (ho : c.output = []) :
    ∃ c' k, Exec (inp d) W (.seq reachStart (.whileLtN 26 2 pass)) c c' k ∧
      WordsBounded W c' ∧ Regs d c' ∧ c'.output = [] ∧ RS d (nv d) c'.nmem ∧
      c'.nreg 25 = nv d ∧ k ≤ (22 * nd d + 6) * nv d + 6 := by
  obtain ⟨c₁, k₁, e₁, hI₁, rfl⟩ := reachStart_exec he c hc hR hm ho
  obtain ⟨c₂, k₂, e₂, hI₂, hn₂, hk₂⟩ := Exec.whileLtN_potential (P := inp d) (W := W) (a := 26)
    (b := 2) (body := pass) (IR d W) (fun c => (nv d - c.nreg 26) * (22 * nd d + 6))
    (fun c h => h.wb) (fun c hc hlt => pass_exec he c hc hlt) hI₁
  have h2 := hI₂.regs.1.2.2.1
  have h26 : c₂.nreg 26 = nv d := by have := hI₂.r26; rw [h2] at hn₂; omega
  have h25 : c₂.nreg 25 = nv d := by
    have := hI₂.cnt; have := hI₂.rs.le; rw [h26] at *; omega
  refine ⟨c₂, _, .seq e₁ e₂, hI₂.wb, hI₂.regs, hI₂.out, h25 ▸ hI₂.rs, h25, ?_⟩
  · have := Nat.sub_le (nv d) (c₁.nreg 26)
    have : (nv d - c₁.nreg 26) * (22 * nd d + 6) ≤ nv d * (22 * nd d + 6) :=
      Nat.mul_le_mul_right _ this
    nlinarith

end Feas

end PlanarFlow
