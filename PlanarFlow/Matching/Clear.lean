module

public import PlanarFlow.Matching.State

/-!
# Maximum bipartite matching on the machine: the start of a phase

The marks of all vertices are cleared and the free white vertices are queued in increasing
order, with time stamps `0, 1, …` (`clear_exec`); this is the initial state of the search.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace BM

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs Finset

variable {d : List ℕ} {W : ℕ}

/-- The state of the clear loop; the matching is `μ`. -/
structure ICl (d : List ℕ) (W : ℕ) (μ : ℕ → ℕ) (c₀ c : Config) : Prop where
  wb : WordsBounded W c
  regs : Regs d c
  keep : ∀ r, (20 ≤ r ∧ r < 22) → c.nreg r = c₀.nreg r
  out : c.output = c₀.output
  mate : ∀ v < nn d, c.nmem v = μ v
  r22 : c.nreg 22 ≤ nn d
  r24 : c.nreg 24 = c.nreg 23
  r25 : c.nreg 25 = 0
  vis : ∀ v < c.nreg 22, vs d c.nmem v = if col d v = 1 ∧ μ v = 0 then 1 else 0
  q : ∀ k < c.nreg 23, qu d c.nmem k < c.nreg 22 ∧ col d (qu d c.nmem k) = 1 ∧
    μ (qu d c.nmem k) = 0 ∧ tmv d c.nmem (qu d c.nmem k) = k
  qinj : ∀ k < c.nreg 23, ∀ l < c.nreg 23, qu d c.nmem k = qu d c.nmem l → k = l
  all : ∀ v < c.nreg 22, col d v = 1 → μ v = 0 → ∃ k < c.nreg 23, qu d c.nmem k = v

lemma ICl.tl {μ : ℕ → ℕ} {c₀ c : Config} (hI : ICl d W μ c₀ c) : c.nreg 23 ≤ c.nreg 22 := by
  classical
  have := Finset.card_le_card_of_injOn (qu d c.nmem) (s := range (c.nreg 23))
    (t := range (c.nreg 22))
    (fun k hk => by simp only [coe_range, Set.mem_Iio] at hk ⊢; exact (hI.q k hk).1)
    (fun k hk l hl e => hI.qinj k (by simpa using hk) l (by simpa using hl) e)
  simpa using this

/-- The vertex `v` is not queued. -/
theorem ICl.skip {μ : ℕ → ℕ} {c₀ c c' : Config} (hI : ICl d W μ c₀ c) {v : ℕ}
    (h22 : c.nreg 22 = v) (hvn : v < nn d) (hnot : ¬ (col d v = 1 ∧ μ v = 0))
    (hw : WordsBounded W c') (hR : Regs d c')
    (hk : ∀ r, (20 ≤ r ∧ r < 22) ∨ r = 23 ∨ r = 24 ∨ r = 25 → c'.nreg r = c.nreg r)
    (ho : c'.output = c.output) (h22' : c'.nreg 22 = v + 1)
    (hm : c'.nmem = upd c.nmem (nn d + v) 0) : ICl d W μ c₀ c' := by
  have hvs : ∀ x, vs d c'.nmem x = if x = v then 0 else vs d c.nmem x := by
    intro x; simp only [vs, hm, upd_apply]; split_ifs <;> first | omega | rfl
  have hqu : ∀ k, qu d c'.nmem k = qu d c.nmem k := by
    intro k; simp only [qu, hm, upd_apply]; split_ifs <;> first | omega | rfl
  have htm : ∀ x, tmv d c'.nmem x = tmv d c.nmem x := by
    intro x; simp only [tmv, hm, upd_apply]; split_ifs <;> first | omega | rfl
  have h23 := hk 23 (by omega)
  have h24 := hk 24 (by omega)
  refine ⟨hw, hR, fun r hr => (hk r (Or.inl hr)).trans (hI.keep r hr), ho.trans hI.out,
    fun x hx => ?_, by omega, by rw [h23, h24]; exact hI.r24, (hk 25 (by omega)).trans hI.r25,
    fun x hx => ?_, fun k hk' => ?_, fun k hk' l hl e => ?_, fun x hx hcx hμx => ?_⟩
  · rw [hm, upd_apply]; split_ifs <;> first | omega | exact hI.mate x hx
  · rw [hvs]
    by_cases hxv : x = v
    · simp only [hxv, ite_true, hnot, ite_false]
    · simp only [hxv, ite_false]; exact hI.vis x (by omega)
  · rw [h23] at hk'
    rw [hqu, htm]
    obtain ⟨a1, a2, a3, a4⟩ := hI.q k hk'
    exact ⟨by omega, a2, a3, a4⟩
  · rw [h23] at hk' hl; rw [hqu, hqu] at e; exact hI.qinj k hk' l hl e
  · rcases Nat.lt_succ_iff_lt_or_eq.1 (h22' ▸ hx) with hx | rfl
    · obtain ⟨k, hk', e⟩ := hI.all x (by omega) hcx hμx
      exact ⟨k, by rw [h23]; exact hk', by rw [hqu]; exact e⟩
    · exact absurd ⟨hcx, hμx⟩ hnot

/-- The vertex `v` is queued. -/
theorem ICl.enq {μ : ℕ → ℕ} {c₀ c c' : Config} (hI : ICl d W μ c₀ c) {v : ℕ}
    (h22 : c.nreg 22 = v) (hvn : v < nn d) (hyes : col d v = 1 ∧ μ v = 0)
    (hw : WordsBounded W c') (hR : Regs d c')
    (hk : ∀ r, (20 ≤ r ∧ r < 22) ∨ r = 25 → c'.nreg r = c.nreg r)
    (ho : c'.output = c.output) (h22' : c'.nreg 22 = v + 1) (h23' : c'.nreg 23 = c.nreg 23 + 1)
    (h24' : c'.nreg 24 = c.nreg 24 + 1)
    (hm : c'.nmem = upd (upd (upd c.nmem (nn d + v) 1) (4 * nn d + c.nreg 23) v)
      (3 * nn d + v) (c.nreg 24)) : ICl d W μ c₀ c' := by
  have htl := hI.tl
  have hvs : ∀ x < nn d, vs d c'.nmem x = if x = v then 1 else vs d c.nmem x := by
    intro x hx; simp only [vs, hm, upd_apply]; split_ifs <;> first | omega | rfl
  have hqu : ∀ k, qu d c'.nmem k = if k = c.nreg 23 then v else qu d c.nmem k := by
    intro k; simp only [qu, hm, upd_apply]; split_ifs <;> first | omega | rfl
  have htm : ∀ x < nn d, tmv d c'.nmem x = if x = v then c.nreg 24 else tmv d c.nmem x := by
    intro x hx; simp only [tmv, hm, upd_apply]; split_ifs <;> first | omega | rfl
  refine ⟨hw, hR, fun r hr => (hk r (Or.inl hr)).trans (hI.keep r hr), ho.trans hI.out,
    fun x hx => ?_, by omega, by rw [h23', h24', hI.r24], (hk 25 (by omega)).trans hI.r25,
    fun x hx => ?_, fun k hk' => ?_, fun k hk' l hl e => ?_, fun x hx hcx hμx => ?_⟩
  · rw [hm]; simp only [upd_apply]; split_ifs <;> first | omega | exact hI.mate x hx
  · rw [hvs x (by omega)]
    by_cases hxv : x = v
    · simp only [hxv, ite_true, hyes, and_self]
    · simp only [hxv, ite_false]; exact hI.vis x (by omega)
  · rw [h23'] at hk'
    rw [hqu]
    by_cases hkt : k = c.nreg 23
    · simp only [hkt, ite_true]
      exact ⟨by omega, hyes.1, hyes.2, by rw [htm v hvn]; simp [hI.r24]⟩
    · simp only [hkt, ite_false]
      obtain ⟨a1, a2, a3, a4⟩ := hI.q k (by omega)
      have hne : qu d c.nmem k ≠ v := by omega
      exact ⟨by omega, a2, a3, by rw [htm _ (by omega)]; simp only [hne, ite_false]; exact a4⟩
  · rw [h23'] at hk' hl
    rw [hqu, hqu] at e
    split_ifs at e with e1 e2 e2
    · omega
    · exact absurd e.symm (by have := (hI.q l (by omega)).1; omega)
    · exact absurd e (by have := (hI.q k (by omega)).1; omega)
    · exact hI.qinj k (by omega) l (by omega) e
  · rcases Nat.lt_succ_iff_lt_or_eq.1 (h22' ▸ hx) with hx | rfl
    · obtain ⟨k, hk', e⟩ := hI.all x (by omega) hcx hμx
      exact ⟨k, by omega, by rw [hqu]; simp only [show k ≠ c.nreg 23 by omega, ite_false]; exact e⟩
    · exact ⟨c.nreg 23, by omega, by rw [hqu]; simp⟩

theorem clearBody_exec (he : Enc d W) {μ : ℕ → ℕ} {c₀ : Config} (c : Config)
    (hI : ICl d W μ c₀ c) (hlt : c.nreg 22 < c.nreg 2) :
    ∃ c' k, Exec (inp d) W clearBody c c' k ∧ ICl d W μ c₀ c' ∧
      (nn d - c'.nreg 22) * 20 + k + 2 ≤ (nn d - c.nreg 22) * 20 := by
  have hc := hI.wb
  have hs := he.size
  obtain ⟨h0, h1, h2, h4, h5, h6, h8, h9, h10⟩ := hI.regs
  rw [h2] at hlt
  obtain ⟨v, hv⟩ : ∃ v, c.nreg 22 = v := ⟨_, rfl⟩
  rw [hv] at hlt
  have hcol := he.col_le v hlt
  have e1 : (inp d).data.getD (c.nreg 22 + c.nreg 6) 0 = col d v := by
    rw [word_inp, hv, h6]; rfl
  have htl := hI.tl
  rw [hv] at htl
  have hmv : upd c.nmem (c.nreg 2 + c.nreg 22) (c.nreg 0) (c.nreg 22) = μ v := by
    rw [upd_other _ _ _ (by omega), hv]; exact hI.mate v hlt
  unfold clearBody
  refine spec_seq ?_
  exec_block
  · config_simp; rw [h2, hv]; omega
  · config_simp; rw [hv, h6]; omega
  · config_simp; exact he.word_le _
  config_simp
  refine spec_seq ?_
  by_cases hyes : col d v = 1 ∧ μ v = 0
  · refine spec_ifLtN_true (by config_simp; rw [e1, h0]; omega) ?_
    refine spec_ifLtN_false (by config_simp; rw [hmv, h0]; omega) ?_
    unfold enq
    exec_block
    · config_simp; rw [h10]; omega
    · config_simp; rw [h9, hv]; omega
    · config_simp; rw [hI.r24]; omega
    · config_simp; omega
    refine spec_instr (Exec.addN ‹_› _ _ _ (by config_simp; rw [h1, hv]; omega)) fun hw => ?_
    refine ⟨hI.enq hv hlt hyes hw (regs_of ⟨h0, h1, h2, h4, h5, h6, h8, h9, h10⟩ fun r hr => by
        config_simp; simp only [upd_apply]; split_ifs <;> first | rfl | omega)
      (fun r hr => by config_simp; simp only [upd_apply]; split_ifs <;> first | rfl | omega)
      (by config_simp) (by config_simp; rw [h1, hv]) (by config_simp; rw [h1])
      (by config_simp; rw [h1])
      (by config_simp; rw [h2, h10, h9, hv]; funext a; simp only [upd_apply]
          split_ifs <;> first | rfl | omega), by config_simp; rw [h1, hv]; omega⟩
  · by_cases hc1 : col d v = 1
    · have hμ : μ v ≠ 0 := fun h => hyes ⟨hc1, h⟩
      refine spec_ifLtN_true (by config_simp; rw [e1, h0]; omega) ?_
      refine spec_ifLtN_true (by config_simp; rw [hmv, h0]; omega) ?_
      refine spec_skip ‹_› ?_
      refine spec_instr (Exec.addN ‹_› _ _ _ (by config_simp; rw [h1]; omega)) fun hw => ?_
      refine ⟨hI.skip hv hlt hyes hw (regs_of ⟨h0, h1, h2, h4, h5, h6, h8, h9, h10⟩ fun r hr => by
          config_simp; simp only [upd_apply]; split_ifs <;> first | rfl | omega)
        (fun r hr => by config_simp; simp only [upd_apply]; split_ifs <;> first | rfl | omega)
        (by config_simp) (by config_simp; rw [h1, hv]) (by config_simp; rw [h2, hv, h0]),
        by config_simp; rw [h1, hv]; omega⟩
    · refine spec_ifLtN_false (by config_simp; rw [e1, h0]; omega) ?_
      refine spec_skip ‹_› ?_
      refine spec_instr (Exec.addN ‹_› _ _ _ (by config_simp; rw [h1]; omega)) fun hw => ?_
      refine ⟨hI.skip hv hlt hyes hw (regs_of ⟨h0, h1, h2, h4, h5, h6, h8, h9, h10⟩ fun r hr => by
          config_simp; simp only [upd_apply]; split_ifs <;> first | rfl | omega)
        (fun r hr => by config_simp; simp only [upd_apply]; split_ifs <;> first | rfl | omega)
        (by config_simp) (by config_simp; rw [h1, hv]) (by config_simp; rw [h2, hv, h0]),
        by config_simp; rw [h1, hv]; omega⟩

/-- The end of the clear loop: the initial state of the search. -/
theorem ICl.toBS {μ : ℕ → ℕ} {c₀ c : Config} (hI : ICl d W μ c₀ c) (h22 : c.nreg 22 = nn d) :
    BS d μ (fun _ => False) c.nmem (c.nreg 23) (c.nreg 23) 0 := by
  classical
  have htl := hI.tl
  rw [h22] at htl
  have hvis : ∀ v < nn d, vs d c.nmem v = if col d v = 1 ∧ μ v = 0 then 1 else 0 :=
    fun v hv => hI.vis v (by omega)
  have hq : ∀ k < c.nreg 23, qu d c.nmem k < nn d := fun k hk => by
    have := (hI.q k hk).1; omega
  refine ⟨hI.mate, fun v hv => by rw [hvis v hv]; split_ifs <;> simp, htl, fun k hk => ?_,
    hI.qinj, fun x hx hcx hvx => ?_, fun x hx hcx hμx => ?_, fun h0 _ _ h => h.elim,
    fun x hx hcx hvx => ?_, fun x hx hcx hvx hμx => ?_, fun v hv hvv => ?_, ?_,
    fun h => absurd rfl h⟩
  · obtain ⟨a1, a2, a3, -⟩ := hI.q k hk
    exact ⟨hq k hk, a2, by rw [hvis _ (hq k hk)]; simp [a2, a3]⟩
  · rw [hvis x hx] at hvx
    have : col d x = 1 ∧ μ x = 0 := by by_contra h; simp [h] at hvx
    exact hI.all x (by omega) this.1 this.2
  · rw [hvis x hx]; simp [hcx, hμx]
  · rw [hvis x hx] at hvx; simp [hcx] at hvx
  · rw [hvis x hx] at hvx; simp [hcx, hμx] at hvx
  · rw [hvis v hv] at hvv
    have : col d v = 1 ∧ μ v = 0 := by by_contra h; simp [h] at hvv
    obtain ⟨k, hk, rfl⟩ := hI.all v (by omega) this.1 this.2
    rw [(hI.q k hk).2.2.2]; exact hk
  · -- the visited vertices are the queued ones
    unfold nvis
    have : (range (nn d)).filter (fun v => vs d c.nmem v = 1) =
        (range (c.nreg 23)).image (qu d c.nmem) := by
      ext v
      simp only [mem_filter, mem_range, mem_image]
      constructor
      · rintro ⟨hv, hvv⟩
        rw [hvis v hv] at hvv
        have : col d v = 1 ∧ μ v = 0 := by by_contra h; simp [h] at hvv
        exact hI.all v (by omega) this.1 this.2
      · rintro ⟨k, hk, rfl⟩
        obtain ⟨-, a2, a3, -⟩ := hI.q k hk
        exact ⟨hq k hk, by rw [hvis _ (hq k hk)]; simp [a2, a3]⟩
    rw [this, card_image_of_injOn (fun k hk l hl e => hI.qinj k (by simpa using hk) l
      (by simpa using hl) e), card_range]

/-- **The clear loop.** -/
theorem clear_exec (he : Enc d W) {μ : ℕ → ℕ} (c : Config) (hc : WordsBounded W c) (hR : Regs d c)
    (hm : ∀ v < nn d, c.nmem v = μ v) (h22 : c.nreg 22 = 0) (h23 : c.nreg 23 = 0)
    (h24 : c.nreg 24 = 0) (h25 : c.nreg 25 = 0) :
    ∃ c' k, Exec (inp d) W (.whileLtN 22 2 clearBody) c c' k ∧ WordsBounded W c' ∧ Regs d c' ∧
      c'.nreg 20 = c.nreg 20 ∧ c'.nreg 21 = c.nreg 21 ∧ c'.output = c.output ∧
      BS d μ (fun _ => False) c'.nmem (c'.nreg 23) (c'.nreg 24) (c'.nreg 25) ∧
      c'.nreg 25 = 0 ∧ k ≤ 20 * nn d + 2 := by
  obtain ⟨c', k, e, hI, hn, hk⟩ := Exec.whileLtN_potential (P := inp d) (W := W) (a := 22)
    (b := 2) (body := clearBody) (ICl d W μ c) (fun c' => (nn d - c'.nreg 22) * 20)
    (fun c h => h.wb) (fun c' hc' hlt => clearBody_exec he c' hc' hlt)
    ⟨hc, hR, fun _ _ => rfl, rfl, hm, by omega, by rw [h24, h23], h25, fun v hv => by omega,
      fun k hk => by omega, fun k hk => by omega, fun v hv => by omega⟩
  have h22' : c'.nreg 22 = nn d := by have := hI.r22; rw [hI.regs.2.2.1] at hn; omega
  refine ⟨c', k, e, hI.wb, hI.regs, hI.keep 20 (by omega), hI.keep 21 (by omega), hI.out, ?_, ?_, ?_⟩
  · rw [hI.r24, hI.r25]; exact hI.toBS h22'
  · exact hI.r25
  · beta_reduce at hk; rw [h22] at hk; omega

end BM

end PlanarFlow
