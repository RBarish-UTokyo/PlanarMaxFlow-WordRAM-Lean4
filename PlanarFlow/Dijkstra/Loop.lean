module

public import PlanarFlow.Dijkstra.Prog

/-!
# Dijkstra's algorithm on the machine: the rounds

The invariant of the rounds (`PlanarFlow.Dijk.IM`): the tree is a tournament tree whose leaves
hold the tentative distances of the vertices not yet done; there is a key `k₀` (the last key
extracted) with every done vertex at distance at most `k₀` and every other vertex at least
`k₀`; the arcs of the done vertices are relaxed; every finite tentative distance is the length
of a walk from the source; the source has distance `0`. Lengths being nonnegative, a relaxation
never lowers the distance of a done vertex, so the arcs of a done vertex stay relaxed.

A round extracts the vertex `v` of least key `k` (`desc`), marks it done, removes it from the
tree and relaxes its arcs (`relax`), each decreased distance being written to its leaf and the
path to the root recomputed. It costs `O((deg v + 1) log n)`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace Dijk

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs Finset Heap

variable {d : List ℕ} {W : ℕ}

lemma off_le_last (he : DEnc d W) {u : ℕ} (hu : u ≤ nn d) : off d u ≤ mm d := by
  have : ∀ k, k ≤ nn d - u → off d (nn d - k) ≤ mm d := by
    intro k hk
    induction k with
    | zero => rw [Nat.sub_zero, he.off_last]
    | succ k ih =>
      have := he.off_mono (nn d - (k + 1)) (by omega)
      rw [show nn d - (k + 1) + 1 = nn d - k by omega] at this
      exact this.trans (ih (by omega))
  have := this (nn d - u) le_rfl
  rwa [show nn d - (nn d - u) = u by omega] at this

lemma arc_lt (he : DEnc d W) {u j : ℕ} (hu : u < nn d) (hj : j < off d (u + 1)) : j < mm d :=
  lt_of_lt_of_le hj (off_le_last he (by omega))

/-- The cost of the rounds still to come, `L = lg (2n)`. -/
def pot (d : List ℕ) (m : ℕ → ℕ) : ℕ :=
  ∑ w ∈ range (nn d), if m (nn d + w) = 0 then
    (23 * lg (2 * nn d) + 21) + (13 * lg (2 * nn d) + 18) * (off d (w + 1) - off d w) else 0

lemma pot_step {m m' : ℕ → ℕ} {v : ℕ} (hv : v < nn d) (h0 : m (nn d + v) = 0)
    (h1 : m' (nn d + v) = 1) (heq : ∀ w < nn d, w ≠ v → m' (nn d + w) = m (nn d + w)) :
    pot d m = pot d m' + ((23 * lg (2 * nn d) + 21) +
      (13 * lg (2 * nn d) + 18) * (off d (v + 1) - off d v)) := by
  unfold pot
  rw [← add_sum_erase _ _ (mem_range.2 hv), ← add_sum_erase _ _ (mem_range.2 hv)]
  have : ∑ w ∈ (range (nn d)).erase v, (if m (nn d + w) = 0 then
      (23 * lg (2 * nn d) + 21) + (13 * lg (2 * nn d) + 18) * (off d (w + 1) - off d w) else 0) =
      ∑ w ∈ (range (nn d)).erase v, (if m' (nn d + w) = 0 then
      (23 * lg (2 * nn d) + 21) + (13 * lg (2 * nn d) + 18) * (off d (w + 1) - off d w) else 0) :=
    sum_congr rfl fun w hw => by
      rw [heq w (mem_range.1 (mem_of_mem_erase hw)) (ne_of_mem_erase hw)]
  rw [this]; simp [h0, h1]; ring

/-- The state between rounds. -/
structure IM (d : List ℕ) (W : ℕ) (c : Config) : Prop where
  wb : WordsBounded W c
  regs : Regs d c
  out : c.output = []
  tour : IsTour (nn d) (tv d c.nmem)
  leaf : ∀ w < nn d, tv d c.nmem (nn d + w) = if c.nmem (nn d + w) = 1 then inf d else c.nmem w
  done01 : ∀ w < nn d, c.nmem (nn d + w) = 0 ∨ c.nmem (nn d + w) = 1
  dle : ∀ w < nn d, c.nmem w ≤ inf d
  key : ∃ k₀, (∀ w < nn d, c.nmem (nn d + w) = 1 → c.nmem w ≤ k₀) ∧
    (∀ w < nn d, c.nmem (nn d + w) = 0 → k₀ ≤ c.nmem w)
  relaxed : ∀ u < nn d, c.nmem (nn d + u) = 1 → ∀ j, off d u ≤ j → j < off d (u + 1) →
    c.nmem (dst d j) ≤ c.nmem u + len d j
  reach : ∀ w < nn d, c.nmem w < inf d → Reach d w (c.nmem w)
  srcz : c.nmem (src d) = 0
  r47 : c.nreg 47 = tv d c.nmem 1

/-- The state while relaxing the arcs of `v`, extracted with key `k`; `D` the done marks. -/
structure IRx (d : List ℕ) (W : ℕ) (v k : ℕ) (D : ℕ → ℕ) (c : Config) : Prop where
  wb : WordsBounded W c
  regs : Regs d c
  out : c.output = []
  r47 : c.nreg 47 = k
  r49 : c.nreg 49 = v
  r51 : c.nreg 51 = off d (v + 1)
  r50lo : off d v ≤ c.nreg 50
  r50hi : c.nreg 50 ≤ off d (v + 1)
  vn : v < nn d
  tour : IsTour (nn d) (tv d c.nmem)
  leaf : ∀ w < nn d, tv d c.nmem (nn d + w) = if c.nmem (nn d + w) = 1 then inf d else c.nmem w
  dn : ∀ w < nn d, c.nmem (nn d + w) = D w
  dnv : D v = 1
  done01 : ∀ w < nn d, D w = 0 ∨ D w = 1
  dle : ∀ w < nn d, c.nmem w ≤ inf d
  distv : c.nmem v = k
  klt : k < inf d
  kdone : ∀ w < nn d, D w = 1 → c.nmem w ≤ k
  knot : ∀ w < nn d, D w = 0 → k ≤ c.nmem w
  relaxed : ∀ u < nn d, D u = 1 → u ≠ v → ∀ j, off d u ≤ j → j < off d (u + 1) →
    c.nmem (dst d j) ≤ c.nmem u + len d j
  relv : ∀ j, off d v ≤ j → j < c.nreg 50 → c.nmem (dst d j) ≤ k + len d j
  reach : ∀ w < nn d, c.nmem w < inf d → Reach d w (c.nmem w)
  srcz : c.nmem (src d) = 0

/-- One relaxation, on the memory. -/
theorem IRx.next (he : DEnc d W) {v k : ℕ} {D : ℕ → ℕ} {c c' : Config} (hI : IRx d W v k D c)
    (hlt : c.nreg 50 < off d (v + 1)) (hw : WordsBounded W c') (hR : Regs d c')
    (hout : c'.output = []) (h47 : c'.nreg 47 = k) (h49 : c'.nreg 49 = v)
    (h51 : c'.nreg 51 = off d (v + 1)) (h50 : c'.nreg 50 = c.nreg 50 + 1)
    (hT : IsTour (nn d) (tv d c'.nmem))
    (hleaf : ∀ x < nn d, tv d c'.nmem (nn d + x) =
      if c'.nmem (nn d + x) = 1 then inf d else c'.nmem x)
    (hdn : ∀ x < nn d, c'.nmem (nn d + x) = c.nmem (nn d + x))
    (hdist : ∀ x < nn d, c'.nmem x = if len d (c.nreg 50) + k < c.nmem (dst d (c.nreg 50)) ∧
      x = dst d (c.nreg 50) then len d (c.nreg 50) + k else c.nmem x) :
    IRx d W v k D c' := by
  have hvn := hI.vn
  generalize hj : c.nreg 50 = j at hlt hdist h50
  have hjm := arc_lt he hvn hlt
  have hjlo : off d v ≤ j := hj ▸ hI.r50lo
  have hwn := he.dst_lt j hjm
  have hk := hI.klt
  have hle : ∀ x < nn d, c'.nmem x ≤ c.nmem x := by
    intro x hx; rw [hdist x hx]; split_ifs with h
    · rw [h.2]; omega
    · exact le_rfl
  have hwnot : len d j + k < c.nmem (dst d j) → D (dst d j) = 0 := by
    intro h
    rcases hI.done01 _ hwn with h' | h'
    · exact h'
    · have := hI.kdone _ hwn h'; omega
  refine ⟨hw, hR, hout, h47, h49, h51, by omega, by omega, hvn, hT, hleaf,
    fun x hx => (hdn x hx).trans (hI.dn x hx), hI.dnv, hI.done01,
    fun x hx => (hle x hx).trans (hI.dle x hx), ?_, hk, fun x hx h => (hle x hx).trans
    (hI.kdone x hx h), fun x hx h => ?_, fun u hu hDu huv j' h1 h2 => ?_, fun j' h1 h2 => ?_,
    fun x hx hlt' => ?_, ?_⟩
  · rw [hdist v hvn]; split_ifs with h
    · have := hwnot h.1; rw [← h.2, hI.dnv] at this; omega
    · exact hI.distv
  · rw [hdist x hx]; split_ifs with h'
    · omega
    · exact hI.knot x hx h
  · have hjm' := arc_lt he hu h2
    have := hI.relaxed u hu hDu huv j' h1 h2
    rw [hdist u hu]
    have hu' : ¬ (len d j + k < c.nmem (dst d j) ∧ u = dst d j) := fun h => by
      have := hwnot h.1; rw [← h.2] at this; omega
    simp only [hu', ite_false]
    exact (hle _ (he.dst_lt j' hjm')).trans this
  · rw [h50] at h2
    rcases Nat.lt_succ_iff_lt_or_eq.1 h2 with h2 | h2
    · exact (hle _ (he.dst_lt j' (arc_lt he hvn (by omega)))).trans (hI.relv j' h1 (by omega))
    · subst h2
      rw [hdist _ hwn]; split_ifs with h
      · omega
      · omega
  · rw [hdist x hx] at hlt' ⊢
    split_ifs with h
    · rw [h.2]
      have hv' : c.nmem v < inf d := by rw [hI.distv]; exact hk
      have := Reach.step (hI.reach v hvn hv') hvn hjlo hlt
      rw [hI.distv, Nat.add_comm] at this; exact this
    · simp only [h, ite_false] at hlt'; exact hI.reach x hx hlt'
  · rw [hdist _ (he.src_lt)]; split_ifs with h
    · have := hI.srcz; rw [h.2] at this; omega
    · exact hI.srcz

theorem relax_exec (he : DEnc d W) {v k : ℕ} {D : ℕ → ℕ} (c : Config) (hI : IRx d W v k D c)
    (hlt : c.nreg 50 < c.nreg 51) :
    ∃ c' k', Exec (inp d) W relax c c' k' ∧ IRx d W v k D c' ∧
      (off d (v + 1) - c'.nreg 50) * (13 * lg (2 * nn d) + 18) + k' + 2 ≤
        (off d (v + 1) - c.nreg 50) * (13 * lg (2 * nn d) + 18) := by
  have hc := hI.wb
  have hs := he.size
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩ := hI.regs
  have hvn := hI.vn
  rw [hI.r51] at hlt
  have hjm := arc_lt he hvn hlt
  have hjlo : off d v ≤ (c.nreg 50) := hI.r50lo
  generalize hw : dst d (c.nreg 50) = w
  have hwn : w < nn d := hw ▸ he.dst_lt (c.nreg 50) hjm
  have hlen := he.inf_le (c.nreg 50) hjm
  have hk := hI.klt
  have e1 : word d ((c.nreg 50) * 2 + (nn d + 5)) = w := hw
  have e2 : word d ((c.nreg 50) * 2 + (nn d + 5) + 1) = len d (c.nreg 50) := rfl
  have hwl := he.word_le ((c.nreg 50) * 2 + (nn d + 5) + 1)
  rw [e2] at hwl
  have hL : lg ((nn d + w) / 2) ≤ lg (2 * nn d) := lg_mono (by omega)
  unfold relax
  refine spec_seq ?_
  exec_block
  · config_simp; rw [h6]; omega
  · config_simp; rw [h6, h5]; omega
  · config_simp; exact he.word_le _
  · config_simp; rw [h6, h5]; omega
  · config_simp; exact he.word_le _
  · config_simp; rw [h6, h5, h1, word_inp, e2, hI.r47]; omega
  simp only [h1, h5, h6, word_inp, e1, e2, hI.r47] at *
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩ := hI.regs
  have hww := hI.dle w hwn
  refine spec_seq ?_
  by_cases hcmp : len d (c.nreg 50) + k < c.nmem w
  · -- the distance of `w` decreases
    have hwnot : D w = 0 := by
      rcases hI.done01 w hwn with h | h
      · exact h
      · have := hI.kdone w hwn h; omega
    refine spec_ifLtN_true (by config_simp; exact hcmp) ?_
    refine spec_seq ?_
    exec_block
    any_goals (config_simp; simp only [h2, h4]; omega)
    config_simp
    have hMa : ∀ a, (upd (upd c.nmem w (len d (c.nreg 50) + k)) (c.nreg 4 + (c.nreg 2 + w)) (len d (c.nreg 50) + k)) a =
        if a = 2 * nn d + (nn d + w) then len d (c.nreg 50) + k else if a = w then len d (c.nreg 50) + k
        else c.nmem a := by
      intro a; rw [upd_apply, upd_apply, h2, h4]
      all_goals (split_ifs <;> first | rfl | omega)
    have hexc : IsTourExc (nn d) (tv d (upd (upd c.nmem w (len d (c.nreg 50) + k))
        (c.nreg 4 + (c.nreg 2 + w)) (len d (c.nreg 50) + k))) ((c.nreg 2 + w) / c.nreg 6) := by
      have e : (c.nreg 2 + w) / c.nreg 6 = (nn d + w) / 2 := by rw [h2, h6]
      rw [e]
      exact isTourExc_set hI.tour (by omega) fun a ha => by
        simp only [tv, hMa]; (try split_ifs) <;> first | omega | rfl
    obtain ⟨c₂, k₂, e₂, hw₂, hK₂, ho₂, hT₂, hf₂, hk₂⟩ := upd_exec he _ ‹_›
      (regs_of ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩ fun r hr => by
        config_simp; simp only [upd_apply]; split_ifs <;> first | rfl | omega)
      (by config_simp; rw [h2, h6]; omega) (by config_simp; exact hexc)
    config_simp at hf₂
    config_simp at hk₂
    config_simp at ho₂
    refine ⟨c₂, k₂, e₂, ?_⟩
    have hK : ∀ r, (r < 40 ∨ 46 ≤ r) → r ≠ 48 → r ≠ 52 → r ≠ 53 → r ≠ 54 →
        c₂.nreg r = c.nreg r := by
      intro r hr a b e f
      rw [hK₂ r hr]; config_simp; simp only [upd_apply]; split_ifs <;> first | omega | rfl
    have hmem : ∀ x < nn d, c₂.nmem x = if x = w then len d (c.nreg 50) + k else c.nmem x := by
      intro x hx; rw [hf₂ x (by omega), hMa]; split_ifs <;> first | rfl | omega
    have hdn : ∀ x < nn d, c₂.nmem (nn d + x) = c.nmem (nn d + x) := by
      intro x hx; rw [hf₂ _ (by omega), hMa]; split_ifs <;> first | rfl | omega
    have hlf : ∀ x < nn d, c₂.nmem (2 * nn d + (nn d + x)) =
        if x = w then len d (c.nreg 50) + k else c.nmem (2 * nn d + (nn d + x)) := by
      intro x hx; rw [hf₂ _ (by omega), hMa]; split_ifs <;> first | rfl | omega
    have h50 := hK 50 (by omega) (by omega) (by omega) (by omega) (by omega)
    have h1' : c₂.nreg 1 = 1 := (hK 1 (by omega) (by omega) (by omega) (by omega) (by omega)).trans h1
    refine spec_instr (Exec.addN hw₂ _ _ _ (by rw [h50, h1']; omega)) fun hw₃ => ?_
    have h47 := (hK 47 (by omega) (by omega) (by omega) (by omega) (by omega)).trans hI.r47
    have h49 := (hK 49 (by omega) (by omega) (by omega) (by omega) (by omega)).trans hI.r49
    have h51 := (hK 51 (by omega) (by omega) (by omega) (by omega) (by omega)).trans hI.r51
    have hR₃ : Regs d { c₂ with nreg := upd c₂.nreg 50 (c₂.nreg 50 + c₂.nreg 1) } :=
      regs_of ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩ fun r hr => by
        config_simp; rw [upd_other _ _ _ (by omega)]
        exact hK r (by omega) (by omega) (by omega) (by omega) (by omega)
    refine ⟨IRx.next he hI hlt hw₃ hR₃
      (by config_simp; rw [ho₂, hI.out]) (by config_simp; exact h47)
      (by config_simp; exact h49) (by config_simp; exact h51)
      (by config_simp; rw [h50, h1']) (by config_simp; exact hT₂) (fun x hx => ?_)
      (fun x hx => by config_simp; exact hdn x hx) (fun x hx => ?_), ?_⟩
    · config_simp
      simp only [tv]; rw [hlf x hx, hdn x hx, hmem x hx]
      by_cases h1x : x = w
      · subst h1x; rw [hI.dn _ hwn, hwnot]; simp
      · have := hI.leaf x hx; simp only [tv] at this; rw [this]; simp [h1x]
    · config_simp; rw [hmem x hx, hw]
      by_cases hxw : x = w
      · simp [hxw, hcmp]
      · simp [hxw]
    · config_simp; rw [h50, h1']
      have := lg_mono (show (nn d + w) / 2 ≤ 2 * nn d by omega)
      rw [h2, h6] at hk₂
      have hB : (off d (v + 1) - c.nreg 50) * (13 * lg (2 * nn d) + 18) =
          (off d (v + 1) - (c.nreg 50 + 1)) * (13 * lg (2 * nn d) + 18) +
            (13 * lg (2 * nn d) + 18) := by
        rw [← Nat.succ_mul]; congr 1; omega
      rw [hB]
      omega
  · refine spec_ifLtN_false (by config_simp; exact hcmp) ?_
    refine spec_skip ‹_› ?_
    refine spec_instr (Exec.addN ‹_› _ _ _ (by config_simp; omega)) fun hw₃ => ?_
    refine ⟨IRx.next he hI hlt hw₃ ?_
      (by config_simp; exact hI.out) (by config_simp; exact hI.r47) (by config_simp; exact hI.r49)
      (by config_simp; exact hI.r51) (by config_simp; rw [h1]) (by config_simp; exact hI.tour)
      (fun x hx => by config_simp; exact hI.leaf x hx) (fun x hx => by config_simp)
      (fun x hx => by config_simp; rw [hw]; simp [hcmp]), ?_⟩
    · exact regs_of ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩ fun r hr => by
        config_simp; simp only [upd_apply]; split_ifs <;> first | rfl | omega
    config_simp; rw [h1]
    have hB : (off d (v + 1) - c.nreg 50) * (13 * lg (2 * nn d) + 18) =
        (off d (v + 1) - (c.nreg 50 + 1)) * (13 * lg (2 * nn d) + 18) +
          (13 * lg (2 * nn d) + 18) := by
      rw [← Nat.succ_mul]; congr 1; omega
    rw [hB]
    omega

theorem round_exec (he : DEnc d W) (c : Config) (hI : IM d W c) (hlt : c.nreg 47 < c.nreg 3) :
    ∃ c' k', Exec (inp d) W round c c' k' ∧ IM d W c' ∧ pot d c'.nmem + k' + 2 ≤ pot d c.nmem := by
  have hc := hI.wb
  have hs := he.size
  have hn := he.n_pos
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩ := hI.regs
  rw [hI.r47, h3] at hlt
  generalize hk : tv d c.nmem 1 = k at hlt
  -- the descent
  obtain ⟨c₁, k₁, e₁, hw₁, hK₁, ho₁, hm₁, hl1, hl2, hval, hk₁⟩ := desc_exec he c hc hI.regs hI.tour
  generalize hl : c₁.nreg 46 = l at hl1 hl2 hval
  have hR₁ := regs_of hI.regs fun r hr => hK₁ r (Or.inl (by omega))
  obtain ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8⟩ := hR₁
  have hvn : l - nn d < nn d := by omega
  have hleafv := hI.leaf (l - nn d) hvn
  rw [show nn d + (l - nn d) = l by omega, hval, hk] at hleafv
  have hvnot : c.nmem (nn d + (l - nn d)) = 0 := by
    rcases hI.done01 _ hvn with h | h
    · exact h
    · rw [show nn d + (l - nn d) = l by omega] at h; rw [h] at hleafv; simp at hleafv; omega
  have hdistv : c.nmem (l - nn d) = k := by
    rw [show nn d + (l - nn d) = l by omega] at hvnot; rw [hvnot] at hleafv; simp at hleafv
    exact hleafv.symm
  -- marking the vertex done and removing it from the tree
  obtain ⟨c₂, k₂, e₂, hw₂, hpost⟩ : ∃ c₂ k₂, Exec (inp d) W (block [.subN 49 46 2, .addN 48 2 49,
      .storeN 48 1, .addN 48 4 46, .storeN 48 3, .divN 40 46 6]) c₁ c₂ k₂ ∧
      WordsBounded W c₂ ∧ (k₂ = 6 ∧ (∀ r, r ≠ 49 → r ≠ 48 → r ≠ 40 → c₂.nreg r = c₁.nreg r) ∧
        c₂.nreg 49 = l - nn d ∧ c₂.nreg 40 = l / 2 ∧ c₂.output = c₁.output ∧
        c₂.nmem = upd (upd c₁.nmem (nn d + (l - nn d)) 1) (2 * nn d + l) (inf d)) := by
    exec_block
    · config_simp; rw [g2, hl]; omega
    · config_simp; rw [g4, hl]; omega
    refine ⟨‹_›, rfl, fun r a b e => ?_, by config_simp; rw [hl, g2], by config_simp; rw [hl, g6],
      by config_simp, by config_simp; rw [hl, g2, g4, g3, g1]⟩
    config_simp; simp only [upd_apply, a, b, e, ite_false]
  obtain ⟨rfl, hK₂, h49₂, h40₂, ho₂, hm₂⟩ := hpost
  rw [hm₁] at hm₂
  have hexc : IsTourExc (nn d) (tv d c₂.nmem) (c₂.nreg 40) := by
    rw [h40₂]
    exact isTourExc_set hI.tour hl1 fun a ha => by
      simp only [tv, hm₂, upd_apply]; split_ifs <;> first | omega | rfl
  have hR₂ := regs_of ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8⟩ fun r hr =>
    hK₂ r (by omega) (by omega) (by omega)
  obtain ⟨c₃, k₃, e₃, hw₃, hK₃, ho₃, hT₃, hf₃, hk₃⟩ := upd_exec he c₂ hw₂ hR₂
    (by rw [h40₂]; omega) hexc
  have hR₃ := regs_of hR₂ fun r hr => hK₃ r (Or.inl (by omega))
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7, f8⟩ := hR₃
  have h49₃ : c₃.nreg 49 = l - nn d := (hK₃ 49 (Or.inr (by omega))).trans h49₂
  -- the arcs of the vertex
  generalize hv : l - nn d = v at hvn hvnot hdistv h49₂ h49₃ hm₂
  have hoff1 := he.word_le (v + 4)
  have hoff2 := he.word_le (v + 4 + 1)
  obtain ⟨c₄, k₄, e₄, hw₄, hpost⟩ : ∃ c₄ k₄, Exec (inp d) W (block [.addN 48 49 7, .readIn 50 48,
      .addN 48 48 1, .readIn 51 48]) c₃ c₄ k₄ ∧ WordsBounded W c₄ ∧
      (k₄ = 4 ∧ (∀ r, r ≠ 48 → r ≠ 50 → r ≠ 51 → c₄.nreg r = c₃.nreg r) ∧
        c₄.nreg 50 = off d v ∧ c₄.nreg 51 = off d (v + 1) ∧ c₄.output = c₃.output ∧
        c₄.nmem = c₃.nmem) := by
    exec_block
    · config_simp; rw [h49₃, f7]; omega
    · config_simp; exact he.word_le _
    · config_simp; rw [h49₃, f7, f1]; omega
    · config_simp; exact he.word_le _
    refine ⟨‹_›, rfl, fun r a b e => ?_, by config_simp; rw [h49₃, f7, word_inp]; rfl,
      by config_simp; rw [h49₃, f7, f1, word_inp]; rfl, by config_simp, by config_simp⟩
    config_simp; simp only [upd_apply, a, b, e, ite_false]
  obtain ⟨rfl, hK₄, h50₄, h51₄, ho₄, hm₄⟩ := hpost
  have hR₄ := regs_of ⟨f0, f1, f2, f3, f4, f5, f6, f7, f8⟩ fun r hr =>
    hK₄ r (by omega) (by omega) (by omega)
  -- the memory after the extraction
  have hmem : ∀ a, (a < 2 * nn d + 1 ∨ 3 * nn d ≤ a) → c₄.nmem a =
      if a = 2 * nn d + l then inf d else if a = nn d + v then 1 else c.nmem a := by
    intro a ha; rw [hm₄, hf₃ a ha, hm₂]; simp only [upd_apply]
  have hdist : ∀ x < nn d, c₄.nmem x = c.nmem x := by
    intro x hx; rw [hmem x (by omega)]; split_ifs <;> first | rfl | omega
  have hdn : ∀ x < nn d, c₄.nmem (nn d + x) = if x = v then 1 else c.nmem (nn d + x) := by
    intro x hx; rw [hmem _ (by omega)]; split_ifs <;> first | rfl | omega
  obtain ⟨k₀, hk₀1, hk₀2⟩ := hI.key
  have hkv : k₀ ≤ k := by rw [← hdistv]; exact hk₀2 v hvn hvnot
  have hIR : IRx d W v k (fun x => if x = v then 1 else c.nmem (nn d + x)) c₄ := by
    refine ⟨hw₄, hR₄, by rw [ho₄, ho₃, ho₂, ho₁, hI.out], ?_, ?_, h51₄, by rw [h50₄],
      by rw [h50₄]; exact he.off_mono v hvn, hvn, by rw [hm₄]; exact hT₃, fun x hx => ?_,
      hdn, by simp, fun x hx => ?_, fun x hx => by rw [hdist x hx]; exact hI.dle x hx,
      by rw [hdist v hvn]; exact hdistv, hlt, fun x hx h => ?_, fun x hx h => ?_,
      fun u hu hDu huv j h1 h2 => ?_, fun j h1 h2 => by rw [h50₄] at h2; omega,
      fun x hx h => by rw [hdist x hx] at h ⊢; exact hI.reach x hx h,
      by rw [hdist _ he.src_lt]; exact hI.srcz⟩
    · rw [hK₄ 47 (by omega) (by omega) (by omega), hK₃ 47 (Or.inr (by omega)),
        hK₂ 47 (by omega) (by omega) (by omega), hK₁ 47 (Or.inr le_rfl), hI.r47, hk]
    · rw [hK₄ 49 (by omega) (by omega) (by omega), h49₃]
    · simp only [tv]; rw [hmem _ (by omega), hdn x hx, hdist x hx]
      by_cases hxv : x = v
      · subst hxv; simp only [show 2 * nn d + (nn d + x) = 2 * nn d + l by omega, ite_true]
      · have := hI.leaf x hx; simp only [tv] at this
        rw [this]; simp only [hxv, ite_false]
        split_ifs <;> first | omega | rfl
    · by_cases hxv : x = v
      · simp [hxv]
      · simp only [hxv, ite_false]; exact hI.done01 x hx
    · rw [hdist x hx]
      by_cases hxv : x = v
      · subst hxv; omega
      · simp only [hxv, ite_false] at h; exact (hk₀1 x hx h).trans hkv
    · rw [hdist x hx]
      have hxv : x ≠ v := fun e => by subst e; simp at h
      simp only [hxv, ite_false] at h
      have h1 := root_le hI.tour (l := nn d + x) (by omega) (by omega)
      have h2 := hI.leaf x hx
      rw [h, hk] at *
      simp at h2
      omega
    · simp only [huv, ite_false] at hDu
      rw [hdist u hu, hdist _ (he.dst_lt j (arc_lt he hu h2))]
      exact hI.relaxed u hu hDu j h1 h2
  -- the relaxations
  obtain ⟨c₅, k₅, e₅, hI₅, hn₅, hk₅⟩ := Exec.whileLtN_potential (P := inp d) (W := W) (a := 50)
    (b := 51) (body := relax) (IRx d W v k (fun x => if x = v then 1 else c.nmem (nn d + x)))
    (fun c => (off d (v + 1) - c.nreg 50) * (13 * lg (2 * nn d) + 18)) (fun c h => h.wb)
    (fun c hc hlt => relax_exec he c hc hlt) hIR
  have h50₅ : c₅.nreg 50 = off d (v + 1) := by
    have := hI₅.r50hi; rw [hI₅.r51] at hn₅; omega
  obtain ⟨i0, i1, i2, i3, i4, i5, i6, i7, i8⟩ := hI₅.regs
  have hc₅ := hI₅.wb
  obtain ⟨c₆, k₆, e₆, hw₆, hpost⟩ : ∃ c₆ k₆, Exec (inp d) W (block [.addN 48 4 1, .loadN 47 48])
      c₅ c₆ k₆ ∧ WordsBounded W c₆ ∧ (k₆ = 2 ∧ (∀ r, r ≠ 48 → r ≠ 47 → c₆.nreg r = c₅.nreg r) ∧
        c₆.nreg 47 = tv d c₅.nmem 1 ∧ c₆.output = c₅.output ∧ c₆.nmem = c₅.nmem) := by
    exec_block
    · config_simp; rw [i4, i1]; omega
    refine ⟨‹_›, rfl, fun r a b => ?_, by config_simp; rw [i4, i1]; rfl, by config_simp,
      by config_simp⟩
    config_simp; simp only [upd_apply, a, b, ite_false]
  obtain ⟨rfl, hK₆, h47₆, ho₆, hm₆⟩ := hpost
  refine ⟨c₆, _, .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ (.seq e₅ e₆)))), ⟨hw₆,
    regs_of ⟨i0, i1, i2, i3, i4, i5, i6, i7, i8⟩ fun r hr => hK₆ r (by omega) (by omega),
    by rw [ho₆, hI₅.out], by rw [hm₆]; exact hI₅.tour, by rw [hm₆]; exact hI₅.leaf,
    fun x hx => by rw [hm₆, hI₅.dn x hx]; exact hI₅.done01 x hx,
    by rw [hm₆]; exact hI₅.dle, ⟨k, fun x hx h => ?_, fun x hx h => ?_⟩,
    fun u hu hDu j h1 h2 => ?_, by rw [hm₆]; exact hI₅.reach, by rw [hm₆]; exact hI₅.srcz,
    by rw [h47₆, hm₆]⟩, ?_⟩
  · rw [hm₆, hI₅.dn x hx] at h; rw [hm₆]; exact hI₅.kdone x hx h
  · rw [hm₆, hI₅.dn x hx] at h; rw [hm₆]; exact hI₅.knot x hx h
  · rw [hm₆] at hDu ⊢; rw [hI₅.dn u hu] at hDu
    by_cases huv : u = v
    · subst huv; rw [hI₅.distv]; exact hI₅.relv j h1 (by rw [h50₅]; exact h2)
    · exact hI₅.relaxed u hu hDu huv j h1 h2
  · -- the cost
    have hpot := pot_step (d := d) (m := c.nmem) (m' := c₆.nmem) hvn hvnot
      (by rw [hm₆, hI₅.dn v hvn]; simp)
      (fun x hx hxv => by rw [hm₆, hI₅.dn x hx]; simp [hxv])
    have hL1 : lg (c₂.nreg 40) ≤ lg (2 * nn d) := lg_mono (by rw [h40₂]; omega)
    beta_reduce at hk₅
    rw [h50₄] at hk₅
    have : (off d (v + 1) - off d v) * (13 * lg (2 * nn d) + 18) =
        (13 * lg (2 * nn d) + 18) * (off d (v + 1) - off d v) := Nat.mul_comm _ _
    omega

end Dijk

end PlanarFlow
