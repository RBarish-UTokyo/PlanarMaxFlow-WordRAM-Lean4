module

public import PlanarFlow.Matching.Clear

/-!
# Maximum bipartite matching on the machine: the alternating search

The white vertices are taken from the queue in turn and their arcs scanned (`search_exec`).
Every queued vertex is taken at most once and every arc scanned at most once, so a search costs
`O(n + m)` steps.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace BM

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs Finset

variable {d : List ℕ} {W : ℕ}

/-- The out-degree of a vertex. -/
def deg (d : List ℕ) (v : ℕ) : ℕ := off d (v + 1) - off d v

lemma sum_deg (he : Enc d W) : ∀ k ≤ nn d, ∑ v ∈ range k, deg d v = off d k := by
  intro k hk
  induction k with
  | zero => simp [he.off_zero]
  | succ k ih =>
    rw [sum_range_succ, ih (by omega)]
    have := he.off_mono k (by omega)
    unfold deg; omega

/-- The degrees of the vertices taken from the queue add up to at most `m`. -/
def sdeg (d : List ℕ) (m : ℕ → ℕ) (h : ℕ) : ℕ := ∑ k ∈ range h, deg d (qu d m k)

lemma sdeg_le (he : Enc d W) {m : ℕ → ℕ} {h : ℕ} (hq : ∀ k < h, qu d m k < nn d)
    (hinj : ∀ k < h, ∀ l < h, qu d m k = qu d m l → k = l) : sdeg d m h ≤ mm d := by
  classical
  unfold sdeg
  rw [← sum_image (fun k hk l hl e => hinj k (by simpa using hk) l (by simpa using hl) e)]
  calc ∑ x ∈ (range h).image (qu d m), deg d x ≤ ∑ x ∈ range (nn d), deg d x :=
        sum_le_sum_of_subset (fun x hx => by
          obtain ⟨k, hk, rfl⟩ := mem_image.1 hx; exact mem_range.2 (hq k (mem_range.1 hk)))
    _ = mm d := by rw [sum_deg he _ le_rfl, he.off_last]

lemma sdeg_mono {m : ℕ → ℕ} {h h' : ℕ} (hh : h ≤ h') : sdeg d m h ≤ sdeg d m h' :=
  sum_le_sum_of_subset (range_subset_range.2 hh)

lemma off_le_last (he : Enc d W) {u : ℕ} (hu : u ≤ nn d) : off d u ≤ mm d := by
  rw [← he.off_last, ← sum_deg he _ hu, ← sum_deg he _ le_rfl]
  exact sum_le_sum_of_subset (range_subset_range.2 hu)

/-- The state while scanning the arcs of `w`, taken from the queue at position `h₀ - 1`; the
matching `μ` has size `s`. -/
structure IBi (d : List ℕ) (W : ℕ) (μ : ℕ → ℕ) (s : ℕ) (D : ℕ → Prop) (w h₀ : ℕ) (m₀ : ℕ → ℕ)
    (c : Config) : Prop where
  wb : WordsBounded W c
  regs : Regs d c
  out : c.output = []
  r20 : c.nreg 20 = s
  r21 : c.nreg 21 = 1
  bs : BS d μ D c.nmem (c.nreg 23) (c.nreg 24) (c.nreg 25)
  r30 : c.nreg 30 = w
  wn : w < nn d
  wv : vs d c.nmem w = 1
  h0pos : 1 ≤ h₀
  h0le : h₀ ≤ c.nreg 23
  qd : c.nreg 25 = 0 → ∀ k, k + 1 < h₀ → D (qu d c.nmem k)
  qw : qu d c.nmem (h₀ - 1) = w
  qs : ∀ k < h₀, qu d c.nmem k < nn d
  qfix : ∀ k < h₀, qu d c.nmem k = qu d m₀ k
  r22a : c.nreg 25 = 0 → c.nreg 22 = h₀
  r22b : c.nreg 25 ≠ 0 → c.nreg 22 = c.nreg 23
  r32 : c.nreg 32 = off d (w + 1)
  r31lo : off d w ≤ c.nreg 31
  r31hi : c.nreg 31 ≤ off d (w + 1) + 1
  r31a : c.nreg 25 = 0 → c.nreg 31 ≤ off d (w + 1)
  r31b : c.nreg 25 ≠ 0 → c.nreg 31 = off d (w + 1) + 1
  part : c.nreg 25 = 0 → ∀ j, off d w ≤ j → j < c.nreg 31 → vs d c.nmem (dst d j) = 1

/-- The regular registers of the search. -/
def SameR (c c' : Config) (l : List ℕ) : Prop := ∀ r ∈ l, c'.nreg r = c.nreg r

lemma IBi.found0 {μ : ℕ → ℕ} {s : ℕ} {D : ℕ → Prop} {w h₀ : ℕ} {m₀ : ℕ → ℕ} {c : Config}
    (hI : IBi d W μ s D w h₀ m₀ c) (hlt : c.nreg 31 < c.nreg 32) : c.nreg 25 = 0 := by
  by_contra h
  have := hI.r31b h; rw [hI.r32] at hlt; omega

/-- An arc to a visited vertex. -/
theorem IBi.skipArc {μ : ℕ → ℕ} {s : ℕ} {D : ℕ → Prop} {w h₀ : ℕ} {m₀ : ℕ → ℕ} {c c' : Config}
    (hI : IBi d W μ s D w h₀ m₀ c) (hlt : c.nreg 31 < c.nreg 32)
    (hv : vs d c.nmem (dst d (c.nreg 31)) = 1) (hw : WordsBounded W c') (hR : Regs d c')
    (ho : c'.output = []) (hk : SameR c c' [20, 21, 22, 23, 24, 25, 30, 32])
    (h31 : c'.nreg 31 = c.nreg 31 + 1) (hm : c'.nmem = c.nmem) : IBi d W μ s D w h₀ m₀ c' := by
  have hf := hI.found0 hlt
  simp only [SameR, List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq] at hk
  obtain ⟨k20, k21, k22, k23, k24, k25, k30, k32⟩ := hk
  have hlt' := hlt; rw [hI.r32] at hlt'
  refine ⟨hw, hR, ho, k20.trans hI.r20, k21.trans hI.r21, by rw [hm, k23, k24, k25]; exact hI.bs,
    k30.trans hI.r30, hI.wn, by rw [hm]; exact hI.wv, hI.h0pos, by rw [k23]; exact hI.h0le,
    fun h => by rw [hm]; rw [k25] at h; exact hI.qd h, by rw [hm]; exact hI.qw,
    by rw [hm]; exact hI.qs, by rw [hm]; exact hI.qfix,
    fun h => by rw [k22]; rw [k25] at h; exact hI.r22a h,
    fun h => by rw [k25] at h; exact absurd hf h, k32.trans hI.r32, by have := hI.r31lo; omega,
    by omega, fun _ => by omega, fun h => by rw [k25] at h; exact absurd hf h, fun _ j h1 h2 => ?_⟩
  rw [hm]
  rcases Nat.lt_succ_iff_lt_or_eq.1 (h31 ▸ h2) with h2 | rfl
  · exact hI.part hf j h1 h2
  · exact hv

/-- An arc to an unvisited matched black vertex: its mate is queued. -/
theorem IBi.matched (he : Enc d W) {μ : ℕ → ℕ} (hμ : Valid d μ) {s : ℕ} {D : ℕ → Prop}
    {w h₀ : ℕ} {m₀ : ℕ → ℕ} {c c' : Config} (hI : IBi d W μ s D w h₀ m₀ c) (hlt : c.nreg 31 < c.nreg 32)
    (hv : vs d c.nmem (dst d (c.nreg 31)) = 0) (hmb : μ (dst d (c.nreg 31)) ≠ 0)
    (hw : WordsBounded W c') (hR : Regs d c') (ho : c'.output = [])
    (hk : SameR c c' [20, 21, 22, 25, 30, 32]) (h31 : c'.nreg 31 = c.nreg 31 + 1)
    (h23 : c'.nreg 23 = c.nreg 23 + 1) (h24 : c'.nreg 24 = c.nreg 24 + 2)
    (hm : c'.nmem = enqMem d (visitMem d c.nmem w (dst d (c.nreg 31)) (c.nreg 24))
      (μ (dst d (c.nreg 31)) - 1) (c.nreg 23) (c.nreg 24 + 1)) : IBi d W μ s D w h₀ m₀ c' := by
  have hf := hI.found0 hlt
  simp only [SameR, List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq] at hk
  obtain ⟨k20, k21, k22, k25, k30, k32⟩ := hk
  have hlt' := hlt; rw [hI.r32] at hlt'
  generalize hj : c.nreg 31 = j at *
  have hjlo : off d w ≤ j := hj ▸ hI.r31lo
  have harc : Arc d w (dst d j) := ⟨hI.wn, j, hjlo, hlt', rfl⟩
  have hbs := hI.bs
  rw [hf] at hbs
  obtain ⟨-, hbs'⟩ := hbs.visit_matched he.toWf hμ hI.wn hI.wv harc hv hmb
  have hbn := he.arc_lt _ _ harc
  generalize hb : dst d j = b at *
  have hw'n := (hμ b hbn hmb).1
  -- the queue below the tail and the marks are preserved
  have hqu : ∀ k < c.nreg 23, qu d c'.nmem k = qu d c.nmem k := by
    intro k hk; rw [hm]; simp only [qu, enqMem, visitMem, upd_apply]; split_ifs <;> first | omega | rfl
  have hvs : ∀ x < nn d, vs d c.nmem x = 1 → vs d c'.nmem x = 1 := by
    intro x hx h1; rw [hm]; simp only [vs, enqMem, visitMem, upd_apply] at h1 ⊢
    split_ifs <;> first | rfl | omega | exact h1
  have hh0 := hI.h0le
  refine ⟨hw, hR, ho, k20.trans hI.r20, k21.trans hI.r21, by rw [hm, h23, h24, k25, hf]; exact hbs',
    k30.trans hI.r30, hI.wn, hvs w hI.wn hI.wv, hI.h0pos, by omega,
    fun h k hk => by rw [hqu k (by omega)]; exact hI.qd hf k hk,
    by rw [hqu (h₀ - 1) (by have := hI.h0pos; omega)]; exact hI.qw,
    fun k hk => by rw [hqu k (by omega)]; exact hI.qs k hk,
    fun k hk => by rw [hqu k (by omega)]; exact hI.qfix k hk,
    fun h => by rw [k22]; exact hI.r22a hf, fun h => by rw [k25] at h; exact absurd hf h,
    k32.trans hI.r32, by omega, by omega, fun _ => by omega,
    fun h => absurd (k25.trans hf) h, fun _ j' h1 h2 => ?_⟩
  rcases Nat.lt_succ_iff_lt_or_eq.1 (h31 ▸ h2) with h2 | rfl
  · exact hvs _ (he.arc_lt _ _ ⟨hI.wn, j', h1, by omega, rfl⟩) (hI.part hf j' h1 (by rw [hj]; exact h2))
  · rw [hb, hm]; simp only [vs, enqMem, visitMem, upd_apply]; split_ifs <;> first | rfl | omega

/-- An arc to an unvisited free black vertex: the search stops. -/
theorem IBi.free (he : Enc d W) {μ : ℕ → ℕ} (hμ : Valid d μ) {s : ℕ} {D : ℕ → Prop}
    {w h₀ : ℕ} {m₀ : ℕ → ℕ} {c c' : Config} (hI : IBi d W μ s D w h₀ m₀ c) (hlt : c.nreg 31 < c.nreg 32)
    (hv : vs d c.nmem (dst d (c.nreg 31)) = 0) (hmb : μ (dst d (c.nreg 31)) = 0)
    (hw : WordsBounded W c') (hR : Regs d c') (ho : c'.output = [])
    (hk : SameR c c' [20, 21, 23, 30, 32]) (h31 : c'.nreg 31 = c.nreg 32 + 1)
    (h22 : c'.nreg 22 = c.nreg 23) (h24 : c'.nreg 24 = c.nreg 24 + 1)
    (h25 : c'.nreg 25 = dst d (c.nreg 31) + 1)
    (hm : c'.nmem = visitMem d c.nmem w (dst d (c.nreg 31)) (c.nreg 24)) :
    IBi d W μ s D w h₀ m₀ c' := by
  have hf := hI.found0 hlt
  simp only [SameR, List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq] at hk
  obtain ⟨k20, k21, k23, k30, k32⟩ := hk
  have hlt' := hlt; rw [hI.r32] at hlt'
  generalize hj : c.nreg 31 = j at *
  have hjlo : off d w ≤ j := hj ▸ hI.r31lo
  have harc : Arc d w (dst d j) := ⟨hI.wn, j, hjlo, hlt', rfl⟩
  have hbs := hI.bs
  rw [hf] at hbs
  have hbs' := hbs.visit_free he.toWf hμ hI.wn hI.wv harc hv hmb
  have hqu : ∀ k, qu d c'.nmem k = qu d c.nmem k := by
    intro k; rw [hm]; exact qu_visit (he.arc_lt _ _ harc) k
  have hwv : vs d c'.nmem w = 1 := by
    rw [hm, vs_visit (he.arc_lt _ _ harc) w hI.wn]; split_ifs
    · rfl
    · exact hI.wv
  refine ⟨hw, hR, ho, k20.trans hI.r20, k21.trans hI.r21, by rw [hm, k23, h24, h25]; exact hbs',
    k30.trans hI.r30, hI.wn, hwv, hI.h0pos, by rw [k23]; exact hI.h0le,
    fun h => by rw [h25] at h; omega, by rw [hqu]; exact hI.qw,
    fun k hk => by rw [hqu]; exact hI.qs k hk, fun k hk => by rw [hqu]; exact hI.qfix k hk,
    fun h => by rw [h25] at h; omega,
    fun _ => by rw [h22, k23], k32.trans hI.r32, by rw [h31, hI.r32]; have := hI.r31lo; omega,
    by rw [h31, hI.r32], fun h => by rw [h25] at h; omega, fun _ => by rw [h31, hI.r32],
    fun h => by rw [h25] at h; omega⟩

theorem scanArc_exec (he : Enc d W) {μ : ℕ → ℕ} (hμ : Valid d μ) {s : ℕ} {D : ℕ → Prop}
    {w h₀ : ℕ} {m₀ : ℕ → ℕ} (c : Config) (hI : IBi d W μ s D w h₀ m₀ c)
    (hlt : c.nreg 31 < c.nreg 32) :
    ∃ c' k, Exec (inp d) W scanArc c c' k ∧ IBi d W μ s D w h₀ m₀ c' ∧
      (off d (w + 1) + 1 - c'.nreg 31) * 30 + k + 2 ≤ (off d (w + 1) + 1 - c.nreg 31) * 30 := by
  have hc := hI.wb
  have hs := he.size
  obtain ⟨h0, h1, h2, h4, h5, h6, h8, h9, h10⟩ := hI.regs
  have hwn := hI.wn
  rw [hI.r32] at hlt
  obtain ⟨j, hj⟩ : ∃ j, c.nreg 31 = j := ⟨_, rfl⟩
  rw [hj] at hlt
  have hjlo : off d w ≤ j := hj ▸ hI.r31lo
  have hjm : j < mm d := lt_of_lt_of_le hlt (off_le_last he (by omega))
  have harc : Arc d w (dst d j) := ⟨hwn, j, hjlo, hlt, rfl⟩
  have hbn := he.arc_lt _ _ harc
  have hcb := (he.arc_col _ _ harc).2
  have e1 : (inp d).data.getD (c.nreg 31 + c.nreg 5) 0 = dst d j := by
    rw [word_inp, hj, h5]; rfl
  have hf := hI.found0 (by rw [hj, hI.r32]; exact hlt)
  have hlt0 : c.nreg 31 < c.nreg 32 := by rw [hj, hI.r32]; exact hlt
  have hbs := hI.bs
  have hmu := hbs.mate
  have htn := hbs.tl
  have httn : c.nreg 24 ≤ nn d := by rw [hbs.tcnt]; exact nvis_le _
  have hr30 := hI.r30
  have h32m : c.nreg 32 ≤ mm d := by rw [hI.r32]; exact off_le_last he (by omega)
  generalize hb : dst d j = b at harc hbn hcb e1
  unfold scanArc
  refine spec_seq ?_
  exec_block
  · config_simp; rw [hj, h5]; omega
  · config_simp; exact he.word_le _
  · config_simp; rw [e1, h2]; omega
  config_simp
  rw [e1, h2] at *
  obtain ⟨h0, h1, h2, h4, h5, h6, h8, h9, h10⟩ := hI.regs
  refine spec_seq ?_
  rcases hbs.vis01 b hbn with hv0 | hv1
  · -- a new black vertex
    have hv0' : c.nmem (nn d + b) = 0 := hv0
    refine spec_ifLtN_true (by config_simp; rw [hv0', h1]; omega) ?_
    unfold visitB
    refine spec_seq ?_
    exec_block
    · config_simp; rw [h8]; omega
    · config_simp; rw [h9]; omega
    · config_simp; omega
    config_simp
    have hmb : upd (upd (upd c.nmem (nn d + b) (c.nreg 1)) (c.nreg 8 + b) (c.nreg 30))
        (c.nreg 9 + b) (c.nreg 24) b = μ b := by
      rw [h8, h9]; simp only [upd_apply]; split_ifs <;> first | omega | exact hmu b hbn
    by_cases hm0 : μ b = 0
    · refine spec_ifLtN_false (by config_simp; rw [hmb, h0, hm0]; omega) ?_
      exec_block
      · config_simp; omega
      refine spec_instr (Exec.addN ‹_› _ _ _ (by config_simp; rw [h1]; omega)) fun hw => ?_
      refine ⟨hI.free he hμ hlt0 (by rw [hj, hb]; exact hv0) (by rw [hj, hb]; exact hm0) hw
        (regs_of ⟨h0, h1, h2, h4, h5, h6, h8, h9, h10⟩ fun r hr => by
          config_simp; simp (disch := omega) only [upd_other]) (by
          config_simp; exact hI.out) (by
          simp only [SameR, List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
          refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> config_simp)
        (by config_simp; rw [h1]) (by config_simp) (by config_simp; rw [h1]) (by
          config_simp; rw [hj, hb, h1]) ?_, ?_⟩
      · config_simp; rw [hj, hb, h1, h8, h9, hr30]; rfl
      config_simp; rw [h1]
      have : off d (w + 1) + 1 - (c.nreg 32 + 1) = 0 := by rw [hI.r32]; omega
      rw [this, hj]
      have : (off d (w + 1) + 1 - j) * 30 ≥ 2 * 30 := Nat.mul_le_mul_right _ (by omega)
      omega
    · have hm0' : 0 < μ b := Nat.pos_of_ne_zero hm0
      obtain ⟨hw'0, -⟩ := (hf ▸ hbs).visit_matched he.toWf hμ hI.wn hI.wv harc hv0 hm0
      have hw'n := (hμ b hbn hm0).1
      have hbw' : μ b - 1 ≠ b := fun e => by
        have := (he.arc_col _ _ ((hμ b hbn hm0).2.2.2 hcb)).1; rw [e] at this; omega
      refine spec_ifLtN_true (by config_simp; rw [hmb, h0]; omega) ?_
      refine spec_seq ?_
      exec_block
      · config_simp; rw [h2]; omega
      config_simp
      have hvw' : upd (upd (upd c.nmem (nn d + b) (c.nreg 1)) (c.nreg 8 + b) (c.nreg 30))
          (c.nreg 9 + b) (c.nreg 24) (c.nreg 2 + (μ b - c.nreg 1)) = 0 := by
        rw [h8, h9, h2, h1]; simp only [upd_apply]; split_ifs <;> first | omega | exact hw'0
      refine spec_ifLtN_true (by config_simp; rw [hmb, hvw', h1]; omega) ?_
      unfold enqW
      exec_block
      · config_simp; rw [h10]; have := hbs.tail_lt hw'n hw'0; omega
      · config_simp; rw [hmb, h9, h1]; omega
      · config_simp; omega
      · config_simp; have := hbs.tail_lt hw'n hw'0; omega
      refine spec_instr (Exec.addN ‹_› _ _ _ (by config_simp; rw [h1]; omega)) fun hw => ?_
      refine ⟨hI.matched he hμ hlt0 (by rw [hj, hb]; exact hv0) (by rw [hj, hb]; exact hm0) hw
        (regs_of ⟨h0, h1, h2, h4, h5, h6, h8, h9, h10⟩ fun r hr => by
          config_simp; simp (disch := omega) only [upd_other]) (by
          config_simp; exact hI.out) (by
          simp only [SameR, List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> config_simp)
        (by config_simp; rw [h1]) (by config_simp; rw [h1]) (by config_simp; rw [h1]) ?_, ?_⟩
      · config_simp; rw [hmb, hj, hb, h1, h2, h8, h9, h10, hr30]; rfl
      config_simp; rw [h1, hj]
      have : (off d (w + 1) + 1 - j) * 30 = (off d (w + 1) + 1 - (j + 1)) * 30 + 30 := by
        rw [← Nat.succ_mul]; congr 1; omega
      omega
  · -- a visited black vertex
    have hv1' : c.nmem (nn d + b) = 1 := hv1
    refine spec_ifLtN_false (by config_simp; rw [hv1', h1]; omega) ?_
    refine spec_skip ‹_› ?_
    refine spec_instr (Exec.addN ‹_› _ _ _ (by config_simp; rw [h1]; omega)) fun hw => ?_
    refine ⟨hI.skipArc hlt0 (by rw [hj, hb]; exact hv1) hw
      (regs_of ⟨h0, h1, h2, h4, h5, h6, h8, h9, h10⟩ fun r hr => by
        config_simp; simp (disch := omega) only [upd_other]) (by
        config_simp; exact hI.out) (by
        simp only [SameR, List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> config_simp)
      (by config_simp; rw [h1]) (by config_simp), ?_⟩
    config_simp; rw [h1, hj]
    have : (off d (w + 1) + 1 - j) * 30 = (off d (w + 1) + 1 - (j + 1)) * 30 + 30 := by
      rw [← Nat.succ_mul]; congr 1; omega
    omega

/-- The state between two white vertices of the search. -/
structure IBo (d : List ℕ) (W : ℕ) (μ : ℕ → ℕ) (s : ℕ) (c : Config) : Prop where
  wb : WordsBounded W c
  regs : Regs d c
  out : c.output = []
  r20 : c.nreg 20 = s
  r21 : c.nreg 21 = 1
  bs : ∃ D, BS d μ D c.nmem (c.nreg 23) (c.nreg 24) (c.nreg 25) ∧
    (c.nreg 25 = 0 → ∀ k < c.nreg 22, D (qu d c.nmem k))
  hl : c.nreg 22 ≤ c.nreg 23
  hf : c.nreg 25 ≠ 0 → c.nreg 22 = c.nreg 23

/-- The potential of the search. -/
def potS (d : List ℕ) (c : Config) : ℕ :=
  41 * (nn d - c.nreg 22) + 30 * (mm d - sdeg d c.nmem (c.nreg 22))

theorem bfsBody_exec (he : Enc d W) {μ : ℕ → ℕ} (hμ : Valid d μ) {s : ℕ} (c : Config)
    (hI : IBo d W μ s c) (hlt : c.nreg 22 < c.nreg 23) :
    ∃ c' k, Exec (inp d) W (.seq deq (.whileLtN 31 32 scanArc)) c c' k ∧ IBo d W μ s c' ∧
      potS d c' + k + 2 ≤ potS d c := by
  have hc := hI.wb
  have hs := he.size
  obtain ⟨h0, h1, h2, h4, h5, h6, h8, h9, h10⟩ := hI.regs
  obtain ⟨D, hbs, hD⟩ := hI.bs
  have hf0 : c.nreg 25 = 0 := by
    by_contra h; have := hI.hf h; omega
  obtain ⟨hwn, hwc, hwv⟩ := hbs.q _ hlt
  generalize hw : qu d c.nmem (c.nreg 22) = w at hwn hwc hwv
  have htl := hbs.tl
  have hoff := he.off_mono w hwn
  have hoffm := off_le_last he (u := w + 1) (by omega)
  have e1 : (inp d).data.getD (w + c.nreg 4) 0 = off d w := by rw [word_inp, h4]; rfl
  have e2 : (inp d).data.getD (w + c.nreg 4 + c.nreg 1) 0 = off d (w + 1) := by
    rw [word_inp, h4, h1]; unfold off; congr 1; omega
  have hmw : c.nmem (c.nreg 10 + c.nreg 22) = w := by rw [h10]; exact hw
  -- taking the vertex from the queue
  obtain ⟨c₁, k₁, e₁, hw₁, hpost⟩ : ∃ c₁ k₁, Exec (inp d) W deq c c₁ k₁ ∧ WordsBounded W c₁ ∧
      (k₁ = 7 ∧ (∀ r, r ≠ 22 → r ≠ 26 → r ≠ 30 → r ≠ 31 → r ≠ 32 → c₁.nreg r = c.nreg r) ∧
        c₁.nreg 22 = c.nreg 22 + 1 ∧ c₁.nreg 30 = w ∧ c₁.nreg 31 = off d w ∧
        c₁.nreg 32 = off d (w + 1) ∧ c₁.nmem = c.nmem ∧ c₁.output = c.output) := by
    unfold deq
    exec_block
    · config_simp; rw [h10]; omega
    · config_simp; rw [h1]; omega
    · config_simp; rw [hmw, h4]; omega
    · config_simp; exact he.word_le _
    · config_simp; rw [hmw, h4, h1]; omega
    · config_simp; exact he.word_le _
    refine ⟨‹_›, rfl, fun r a b e f g => ?_, by config_simp; rw [h1], by config_simp; rw [hmw],
      by config_simp; rw [hmw, e1], by config_simp; rw [hmw, e2], by config_simp, by config_simp⟩
    config_simp; simp (disch := omega) only [upd_other]
  obtain ⟨rfl, hK₁, h22₁, h30₁, h31₁, h32₁, hm₁, ho₁⟩ := hpost
  have hR₁ := regs_of ⟨h0, h1, h2, h4, h5, h6, h8, h9, h10⟩ fun r hr =>
    hK₁ r (by omega) (by omega) (by omega) (by omega) (by omega)
  have hJ : IBi d W μ s D w (c.nreg 22 + 1) c.nmem c₁ := by
    rw [← hm₁] at hbs hD hwv
    refine ⟨hw₁, hR₁, ho₁.trans hI.out, (hK₁ 20 (by omega) (by omega) (by omega) (by omega)
      (by omega)).trans hI.r20, (hK₁ 21 (by omega) (by omega) (by omega) (by omega)
      (by omega)).trans hI.r21, ?_, h30₁, hwn, hwv, by omega, ?_, fun h k hk => ?_, ?_,
      fun k hk => ?_, fun k hk => by rw [hm₁], fun _ => h22₁, fun h => ?_, h32₁, by rw [h31₁],
      by rw [h31₁]; omega, fun _ => by rw [h31₁]; exact hoff, fun h => ?_,
      fun _ j h1 h2 => by rw [h31₁] at h2; omega⟩
    · rw [hK₁ 23 (by omega) (by omega) (by omega) (by omega) (by omega),
        hK₁ 24 (by omega) (by omega) (by omega) (by omega) (by omega),
        hK₁ 25 (by omega) (by omega) (by omega) (by omega) (by omega)]; exact hbs
    · rw [hK₁ 23 (by omega) (by omega) (by omega) (by omega) (by omega)]; omega
    · exact hD hf0 k (by omega)
    · rw [hm₁]; simpa using hw
    · exact (hbs.q k (by omega)).1
    · rw [hK₁ 25 (by omega) (by omega) (by omega) (by omega) (by omega)] at h; exact absurd hf0 h
    · rw [hK₁ 25 (by omega) (by omega) (by omega) (by omega) (by omega)] at h; exact absurd hf0 h
  -- scanning the arcs
  obtain ⟨c₂, k₂, e₂, hJ₂, hn₂, hk₂⟩ := Exec.whileLtN_potential (P := inp d) (W := W) (a := 31)
    (b := 32) (body := scanArc) (IBi d W μ s D w (c.nreg 22 + 1) c.nmem)
    (fun c => (off d (w + 1) + 1 - c.nreg 31) * 30) (fun c h => h.wb)
    (fun c hc hlt => scanArc_exec he hμ c hc hlt) hJ
  have hall : c₂.nreg 25 = 0 → ∀ b, Arc d w b → vs d c₂.nmem b = 1 := by
    intro h0' b ⟨_, j, hj1, hj2, hjb⟩
    have h31 := hJ₂.r31a h0'
    rw [hJ₂.r32] at hn₂
    rw [← hjb]; exact hJ₂.part h0' j hj1 (by omega)
  have hbs₂ := hJ₂.bs.done hall
  refine ⟨c₂, 7 + k₂, .seq e₁ e₂, ⟨hJ₂.wb, hJ₂.regs, hJ₂.out, hJ₂.r20, hJ₂.r21,
    ⟨_, hbs₂, fun h0' k hk => ?_⟩, ?_, fun h => hJ₂.r22b h⟩, ?_⟩
  · rw [hJ₂.r22a h0'] at hk
    rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
    · exact Or.inl (hJ₂.qd h0' k (by omega))
    · right; exact hJ₂.qw
  · by_cases h0' : c₂.nreg 25 = 0
    · rw [hJ₂.r22a h0']; exact hJ₂.h0le
    · rw [hJ₂.r22b h0']
  · -- the potential
    unfold potS
    have hh : c.nreg 22 + 1 ≤ c₂.nreg 22 := by
      by_cases h0' : c₂.nreg 25 = 0
      · rw [hJ₂.r22a h0']
      · rw [hJ₂.r22b h0']; exact hJ₂.h0le
    have hbs₂' := hJ₂.bs
    have hs1 : sdeg d c₂.nmem (c.nreg 22 + 1) = sdeg d c.nmem (c.nreg 22) + deg d w := by
      unfold sdeg; rw [sum_range_succ]
      congr 1
      · exact sum_congr rfl fun k hk => by
          rw [hJ₂.qfix k (by have := mem_range.1 hk; omega)]
      · rw [hJ₂.qfix _ (by omega), hw]
    have hs2 : sdeg d c₂.nmem (c₂.nreg 22) ≤ mm d := by
      have h22le : c₂.nreg 22 ≤ c₂.nreg 23 := by
        by_cases h0' : c₂.nreg 25 = 0
        · rw [hJ₂.r22a h0']; exact hJ₂.h0le
        · rw [hJ₂.r22b h0']
      exact sdeg_le he (fun k hk => (hbs₂'.q k (by omega)).1)
        (fun k hk l hl e => hbs₂'.qinj k (by omega) l (by omega) e)
    have hs3 := sdeg_mono (d := d) (m := c₂.nmem) hh
    beta_reduce at hk₂
    rw [h31₁] at hk₂
    have hdeg : (off d (w + 1) + 1 - off d w) * 30 = 30 * deg d w + 30 := by
      unfold deg; rw [show off d (w + 1) + 1 - off d w = off d (w + 1) - off d w + 1 by omega]
      ring
    have hn2 : c₂.nreg 22 ≤ nn d := by
      have := hJ₂.bs.tl
      by_cases h0' : c₂.nreg 25 = 0
      · rw [hJ₂.r22a h0']; have := hJ₂.h0le; omega
      · rw [hJ₂.r22b h0']; exact this
    omega

/-- **The search.** -/
theorem search_exec (he : Enc d W) {μ : ℕ → ℕ} (hμ : Valid d μ) {s : ℕ} (c : Config)
    (hI : IBo d W μ s c) (h22 : c.nreg 22 = 0) :
    ∃ c' k, Exec (inp d) W (.whileLtN 22 23 (.seq deq (.whileLtN 31 32 scanArc))) c c' k ∧
      IBo d W μ s c' ∧ c'.nreg 22 = c'.nreg 23 ∧ k ≤ 41 * nn d + 30 * mm d + 2 := by
  obtain ⟨c', k, e, hI', hn, hk⟩ := Exec.whileLtN_potential (P := inp d) (W := W) (a := 22)
    (b := 23) (body := .seq deq (.whileLtN 31 32 scanArc)) (IBo d W μ s) (potS d)
    (fun c h => h.wb) (fun c hc hlt => bfsBody_exec he hμ c hc hlt) hI
  refine ⟨c', k, e, hI', by have := hI'.hl; omega, ?_⟩
  unfold potS at hk; rw [h22] at hk
  simp only [sdeg, range_zero, sum_empty, Nat.sub_zero] at hk
  omega

end BM

end PlanarFlow
