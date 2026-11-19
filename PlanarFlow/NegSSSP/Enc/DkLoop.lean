module

public import PlanarFlow.NegSSSP.Enc.DkProg

/-!
# Dijkstra's algorithm in memory: the rounds

The invariant of the rounds (`DkIM`, as `PlanarFlow.Dijk.IM` for the program of
`PlanarFlow/Dijkstra/`): the tree is a tournament tree whose leaves hold the tentative distances
of the nodes not yet done; a key `k₀` separates the done nodes (at most `k₀`) from the others
(at least `k₀`); the arcs of the done nodes are relaxed; every finite tentative distance is the
length of a walk from the source (`DkReach`); the source has distance `0`; the memory outside the
written region is the initial one (`m₀`). A round (`dkRound_exec`) extracts the node of least key,
marks it done, removes it from the tree and relaxes its arcs, within `O((deg v + 1) log n)` steps
(the potential `dkPot`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace NegSSSP

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs Finset Heap

variable {P : Input} {W : ℕ}

/-- Changing the value at the leaf `l` breaks the tournament property at most at the ancestors of
`l / 2` (only the nodes below `2n` matter). -/
lemma dk_isTourExc_set {n : ℕ} {t t' : ℕ → ℕ} (h : IsTour n t) {l : ℕ} (hl : n ≤ l)
    (ht : ∀ a < 2 * n, a ≠ l → t' a = t a) : IsTourExc n t' (l / 2) := by
  intro i h1 h2 h3
  have e1 : i ≠ l := by omega
  have e2 : 2 * i ≠ l := fun e => h3 ⟨0, by simp; omega⟩
  have e3 : 2 * i + 1 ≠ l := fun e => h3 ⟨0, by simp; omega⟩
  rw [ht i (by omega) e1, ht _ (by omega) e2, ht _ (by omega) e3]; exact h i h1 h2

/-- The cost of the rounds still to come, `L = lg (2n)`. -/
def dkPot (p : DkP) (m : ℕ → ℕ) : ℕ :=
  ∑ w ∈ range p.n, if m (p.Xb + w) = 0 then
    (23 * lg (2 * p.n) + 21) + (13 * lg (2 * p.n) + 20) * (p.oe w - p.ob w) else 0

lemma dkPot_step {p : DkP} {m m' : ℕ → ℕ} {v : ℕ} (hv : v < p.n) (h0 : m (p.Xb + v) = 0)
    (h1 : m' (p.Xb + v) = 1) (heq : ∀ w < p.n, w ≠ v → m' (p.Xb + w) = m (p.Xb + w)) :
    dkPot p m = dkPot p m' + ((23 * lg (2 * p.n) + 21) +
      (13 * lg (2 * p.n) + 20) * (p.oe v - p.ob v)) := by
  unfold dkPot
  rw [← add_sum_erase _ _ (mem_range.2 hv), ← add_sum_erase _ _ (mem_range.2 hv)]
  have : ∑ w ∈ (range p.n).erase v, (if m (p.Xb + w) = 0 then
      (23 * lg (2 * p.n) + 21) + (13 * lg (2 * p.n) + 20) * (p.oe w - p.ob w) else 0) =
      ∑ w ∈ (range p.n).erase v, (if m' (p.Xb + w) = 0 then
      (23 * lg (2 * p.n) + 21) + (13 * lg (2 * p.n) + 20) * (p.oe w - p.ob w) else 0) :=
    sum_congr rfl fun w hw => by
      rw [heq w (mem_range.1 (mem_of_mem_erase hw)) (ne_of_mem_erase hw)]
  rw [this]; simp [h0, h1]; ring

/-- The state between rounds. -/
structure DkIM (p : DkP) (W : ℕ) (m₀ : ℕ → ℕ) (c : Config) : Prop where
  wb : WordsBounded W c
  regs : DkRegs p c
  fr : ∀ a, ¬ DkOut p a → c.nmem a = m₀ a
  tour : IsTour p.n (dkT p c.nmem)
  leaf : ∀ w < p.n, dkT p c.nmem (p.n + w) =
    if c.nmem (p.Xb + w) = 1 then p.Inf else c.nmem (p.Db + w)
  done01 : ∀ w < p.n, c.nmem (p.Xb + w) = 0 ∨ c.nmem (p.Xb + w) = 1
  dle : ∀ w < p.n, c.nmem (p.Db + w) ≤ p.Inf
  key : ∃ k₀, (∀ w < p.n, c.nmem (p.Xb + w) = 1 → c.nmem (p.Db + w) ≤ k₀) ∧
    (∀ w < p.n, c.nmem (p.Xb + w) = 0 → k₀ ≤ c.nmem (p.Db + w))
  relaxed : ∀ u < p.n, c.nmem (p.Xb + u) = 1 → ∀ j, p.ob u ≤ j → j < p.oe u →
    c.nmem (p.Db + p.nh (p.ol j)) ≤ c.nmem (p.Db + u) + p.ln (p.ol j)
  reach : ∀ w < p.n, c.nmem (p.Db + w) < p.Inf → DkReach p w (c.nmem (p.Db + w))
  srcz : c.nmem (p.Db + p.s) = 0
  r37 : c.nreg 2537 = dkT p c.nmem 1

/-- The state while relaxing the arcs of `v`, extracted with key `k`; `Dn` the done marks. -/
structure DkIRx (p : DkP) (W : ℕ) (m₀ : ℕ → ℕ) (v k : ℕ) (Dn : ℕ → ℕ) (c : Config) : Prop where
  wb : WordsBounded W c
  regs : DkRegs p c
  fr : ∀ a, ¬ DkOut p a → c.nmem a = m₀ a
  r37 : c.nreg 2537 = k
  r39 : c.nreg 2539 = v
  r41 : c.nreg 2541 = p.oe v
  r40lo : p.ob v ≤ c.nreg 2540
  r40hi : c.nreg 2540 ≤ p.oe v
  vn : v < p.n
  tour : IsTour p.n (dkT p c.nmem)
  leaf : ∀ w < p.n, dkT p c.nmem (p.n + w) =
    if c.nmem (p.Xb + w) = 1 then p.Inf else c.nmem (p.Db + w)
  dn : ∀ w < p.n, c.nmem (p.Xb + w) = Dn w
  dnv : Dn v = 1
  done01 : ∀ w < p.n, Dn w = 0 ∨ Dn w = 1
  dle : ∀ w < p.n, c.nmem (p.Db + w) ≤ p.Inf
  distv : c.nmem (p.Db + v) = k
  klt : k < p.Inf
  kdone : ∀ w < p.n, Dn w = 1 → c.nmem (p.Db + w) ≤ k
  knot : ∀ w < p.n, Dn w = 0 → k ≤ c.nmem (p.Db + w)
  relaxed : ∀ u < p.n, Dn u = 1 → u ≠ v → ∀ j, p.ob u ≤ j → j < p.oe u →
    c.nmem (p.Db + p.nh (p.ol j)) ≤ c.nmem (p.Db + u) + p.ln (p.ol j)
  relv : ∀ j, p.ob v ≤ j → j < c.nreg 2540 → c.nmem (p.Db + p.nh (p.ol j)) ≤ k + p.ln (p.ol j)
  reach : ∀ w < p.n, c.nmem (p.Db + w) < p.Inf → DkReach p w (c.nmem (p.Db + w))
  srcz : c.nmem (p.Db + p.s) = 0

/-- One relaxation, on the memory. -/
theorem DkIRx.next {p : DkP} (hG : DkG p W) {m₀ : ℕ → ℕ} {v k : ℕ} {Dn : ℕ → ℕ}
    {c c' : Config} (hI : DkIRx p W m₀ v k Dn c)
    (hlt : c.nreg 2540 < p.oe v) (hw : WordsBounded W c') (hR : DkRegs p c')
    (hfr : ∀ a, ¬ DkOut p a → c'.nmem a = m₀ a)
    (h37 : c'.nreg 2537 = k) (h39 : c'.nreg 2539 = v)
    (h41 : c'.nreg 2541 = p.oe v) (h40 : c'.nreg 2540 = c.nreg 2540 + 1)
    (hT : IsTour p.n (dkT p c'.nmem))
    (hleaf : ∀ x < p.n, dkT p c'.nmem (p.n + x) =
      if c'.nmem (p.Xb + x) = 1 then p.Inf else c'.nmem (p.Db + x))
    (hdn : ∀ x < p.n, c'.nmem (p.Xb + x) = c.nmem (p.Xb + x))
    (hdist : ∀ x < p.n, c'.nmem (p.Db + x) =
      if p.ln (p.ol (c.nreg 2540)) + k < c.nmem (p.Db + p.nh (p.ol (c.nreg 2540))) ∧
        x = p.nh (p.ol (c.nreg 2540)) then p.ln (p.ol (c.nreg 2540)) + k else c.nmem (p.Db + x)) :
    DkIRx p W m₀ v k Dn c' := by
  have hvn := hI.vn
  generalize hj : c.nreg 2540 = j at hlt hdist h40
  have hjlo : p.ob v ≤ j := hj ▸ hI.r40lo
  have hwn := hG.nh_lt v hvn j hjlo hlt
  have hk := hI.klt
  have hle : ∀ x < p.n, c'.nmem (p.Db + x) ≤ c.nmem (p.Db + x) := by
    intro x hx; rw [hdist x hx]; split_ifs with h
    · rw [h.2]; omega
    · exact le_rfl
  have hwnot : p.ln (p.ol j) + k < c.nmem (p.Db + p.nh (p.ol j)) → Dn (p.nh (p.ol j)) = 0 := by
    intro h
    rcases hI.done01 _ hwn with h' | h'
    · exact h'
    · have := hI.kdone _ hwn h'; omega
  refine ⟨hw, hR, hfr, h37, h39, h41, by omega, by omega, hvn, hT, hleaf,
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
  · have := hI.relaxed u hu hDu huv j' h1 h2
    rw [hdist u hu]
    have hu' : ¬ (p.ln (p.ol j) + k < c.nmem (p.Db + p.nh (p.ol j)) ∧ u = p.nh (p.ol j)) :=
      fun h => by have := hwnot h.1; rw [← h.2] at this; omega
    simp only [hu', ite_false]
    exact (hle _ (hG.nh_lt u hu j' h1 h2)).trans this
  · rw [h40] at h2
    rcases Nat.lt_succ_iff_lt_or_eq.1 h2 with h2 | h2
    · exact (hle _ (hG.nh_lt v hvn j' h1 (by omega))).trans (hI.relv j' h1 (by omega))
    · subst h2
      rw [hdist _ hwn]; split_ifs with h
      · omega
      · omega
  · rw [hdist x hx] at hlt' ⊢
    split_ifs with h
    · rw [h.2]
      have hv' : c.nmem (p.Db + v) < p.Inf := by rw [hI.distv]; exact hk
      have := DkReach.step (hI.reach v hvn hv') hvn hjlo hlt
      rw [hI.distv, Nat.add_comm] at this; exact this
    · simp only [h, ite_false] at hlt'; exact hI.reach x hx hlt'
  · rw [hdist _ hG.s_lt]; split_ifs with h
    · have := hI.srcz; rw [h.2] at this; omega
    · exact hI.srcz

set_option maxHeartbeats 1000000 in
theorem dkRelax_exec {p : DkP} (hG : DkG p W) {m₀ : ℕ → ℕ} (hM : DkMem p m₀) {v k : ℕ}
    {Dn : ℕ → ℕ} (c : Config) (hI : DkIRx p W m₀ v k Dn c) (hlt : c.nreg 2540 < c.nreg 2541) :
    ∃ c' k', Exec P W dkRelax c c' k' ∧ DkIRx p W m₀ v k Dn c' ∧
      (p.oe v - c'.nreg 2540) * (13 * lg (2 * p.n) + 20) + k' + 2 ≤
        (p.oe v - c.nreg 2540) * (13 * lg (2 * p.n) + 20) := by
  have hc := hI.wb
  have hX := hG.wX
  have hDw := hG.wD
  have hdx := hG.dDX
  have hM' := hM.of hG hI.fr
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ := hI.regs
  have hvn := hI.vn
  rw [hI.r41] at hlt
  have hjlo : p.ob v ≤ (c.nreg 2540) := hI.r40lo
  have hOL := hG.aOL v hvn _ hjlo hlt
  have hNH := hG.aNH v hvn _ hjlo hlt
  have hLL := hG.aL v hvn _ hjlo hlt
  have eOL := hM'.ol v hvn _ hjlo hlt
  have eNH := hM'.nh v hvn _ hjlo hlt
  have eL := hM'.ln v hvn _ hjlo hlt
  generalize hw : p.nh (p.ol (c.nreg 2540)) = w at eNH
  have hwn : w < p.n := hw ▸ hG.nh_lt v hvn _ hjlo hlt
  have hlen := hG.inf_le v hvn _ hjlo hlt
  have hk := hI.klt
  have hoe : p.oe v ≤ W := by rw [← hM'.oe v hvn]; exact hc.2 _
  have hL : lg ((p.n + w) / 2) ≤ lg (2 * p.n) := lg_mono (by omega)
  unfold dkRelax
  refine spec_seq ?_
  exec_block
  · config_simp; rw [h6]; exact hOL.1
  · config_simp; rw [h7, h6, eOL]; exact hNH.1
  · config_simp; rw [h8, h6, eOL]; exact hLL.1
  · config_simp; rw [h8, h6, eOL, eL, hI.r37]; omega
  · config_simp; rw [h1, h7, h6, eOL, eNH]; omega
  simp only [h1, h6, h7, h8, eOL, eNH, eL, hI.r37] at *
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ := hI.regs
  have hww := hI.dle w hwn
  refine spec_seq ?_
  by_cases hcmp : p.ln (p.ol (c.nreg 2540)) + k < c.nmem (p.Db + w)
  · -- the distance of `w` decreases
    have hwnot : Dn w = 0 := by
      rcases hI.done01 w hwn with h | h
      · exact h
      · have := hI.kdone w hwn h; omega
    refine spec_ifLtN_true (by config_simp; exact hcmp) ?_
    refine spec_seq ?_
    exec_block
    any_goals (config_simp; simp only [h0, h3]; omega)
    config_simp
    have hMa : ∀ a, (upd (upd c.nmem (p.Db + w) (p.ln (p.ol (c.nreg 2540)) + k))
        (c.nreg 2503 + (c.nreg 2500 + w)) (p.ln (p.ol (c.nreg 2540)) + k)) a =
        if a = p.Xb + p.n + (p.n + w) then p.ln (p.ol (c.nreg 2540)) + k
        else if a = p.Db + w then p.ln (p.ol (c.nreg 2540)) + k else c.nmem a := by
      intro a; rw [upd_apply, upd_apply, h0, h3]
      all_goals (split_ifs <;> first | rfl | omega)
    have hexc : IsTourExc p.n (dkT p (upd (upd c.nmem (p.Db + w) (p.ln (p.ol (c.nreg 2540)) + k))
        (c.nreg 2503 + (c.nreg 2500 + w)) (p.ln (p.ol (c.nreg 2540)) + k)))
        ((c.nreg 2500 + w) / c.nreg 2513) := by
      have e : (c.nreg 2500 + w) / c.nreg 2513 = (p.n + w) / 2 := by rw [h0, h13]
      rw [e]
      exact dk_isTourExc_set hI.tour (by omega) fun a ha2 ha => by
        simp only [dkT, hMa]; (try split_ifs) <;> first | omega | rfl
    obtain ⟨c₂, k₂, e₂, hw₂, hK₂, hT₂, hf₂, hk₂⟩ := dkUpd_exec (P := P) hG _ ‹_›
      (dkRegs_of ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ fun r hr hr' => by
        config_simp; simp only [upd_apply]; split_ifs <;> first | rfl | omega)
      (by config_simp; rw [h0, h13]; omega) (by config_simp; exact hexc)
    config_simp at hf₂
    config_simp at hk₂
    refine ⟨c₂, k₂, e₂, ?_⟩
    have hK : ∀ r, (r < 2530 ∨ (2536 ≤ r ∧ r < 2542) ∨ 2548 ≤ r) → c₂.nreg r = c.nreg r := by
      intro r hr
      rw [hK₂ r (by omega)]; config_simp; simp only [upd_apply]; split_ifs <;> first | omega | rfl
    have hmem : ∀ a, (a < p.Xb + p.n + 1 ∨ p.Xb + 2 * p.n ≤ a) → c₂.nmem a =
        if a = p.Xb + p.n + (p.n + w) then p.ln (p.ol (c.nreg 2540)) + k
        else if a = p.Db + w then p.ln (p.ol (c.nreg 2540)) + k else c.nmem a := by
      intro a ha; rw [hf₂ a ha, hMa]
    have hdist : ∀ x < p.n, c₂.nmem (p.Db + x) =
        if x = w then p.ln (p.ol (c.nreg 2540)) + k else c.nmem (p.Db + x) := by
      intro x hx; rw [hmem _ (by omega)]; split_ifs <;> first | rfl | omega
    have hdn : ∀ x < p.n, c₂.nmem (p.Xb + x) = c.nmem (p.Xb + x) := by
      intro x hx; rw [hmem _ (by omega)]; split_ifs <;> first | rfl | omega
    have hlf : ∀ x < p.n, c₂.nmem (p.Xb + p.n + (p.n + x)) =
        if x = w then p.ln (p.ol (c.nreg 2540)) + k else c.nmem (p.Xb + p.n + (p.n + x)) := by
      intro x hx; rw [hmem _ (by omega)]; split_ifs <;> first | rfl | omega
    have hfr₂ : ∀ a, ¬ DkOut p a → c₂.nmem a = m₀ a := by
      intro a ha
      unfold DkOut at ha
      rw [hmem a (by omega)]; split_ifs <;> first | omega | exact hI.fr a ha
    have h40 := hK 2540 (by omega)
    have h12' : c₂.nreg 2512 = 1 := (hK 2512 (by omega)).trans h12
    refine spec_instr (Exec.addN hw₂ _ _ _ (by rw [h40, h12']; omega)) fun hw₃ => ?_
    have h37 := (hK 2537 (by omega)).trans hI.r37
    have h39 := (hK 2539 (by omega)).trans hI.r39
    have h41 := (hK 2541 (by omega)).trans hI.r41
    have hR₃ : DkRegs p { c₂ with nreg := upd c₂.nreg 2540 (c₂.nreg 2540 + c₂.nreg 2512) } :=
      dkRegs_of ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ fun r hr hr' => by
        config_simp; rw [upd_other _ _ _ (by omega)]
        exact hK r (by omega)
    refine ⟨DkIRx.next hG hI hlt hw₃ hR₃ (fun a ha => by config_simp; exact hfr₂ a ha)
      (by config_simp; exact h37)
      (by config_simp; exact h39) (by config_simp; exact h41)
      (by config_simp; rw [h40, h12']) (by config_simp; exact hT₂) (fun x hx => ?_)
      (fun x hx => by config_simp; exact hdn x hx) (fun x hx => ?_), ?_⟩
    · config_simp
      simp only [dkT]; rw [hlf x hx, hdn x hx, hdist x hx]
      by_cases h1x : x = w
      · subst h1x; rw [hI.dn _ hwn, hwnot]; simp
      · have := hI.leaf x hx; simp only [dkT] at this; rw [this]; simp [h1x]
    · config_simp; rw [hdist x hx, hw]
      by_cases hxw : x = w
      · simp [hxw, hcmp]
      · simp [hxw]
    · config_simp; rw [h40, h12']
      have := lg_mono (show (p.n + w) / 2 ≤ 2 * p.n by omega)
      rw [h0, h13] at hk₂
      have hB : (p.oe v - c.nreg 2540) * (13 * lg (2 * p.n) + 20) =
          (p.oe v - (c.nreg 2540 + 1)) * (13 * lg (2 * p.n) + 20) +
            (13 * lg (2 * p.n) + 20) := by
        rw [← Nat.succ_mul]; congr 1; omega
      rw [hB]
      omega
  · refine spec_ifLtN_false (by config_simp; exact hcmp) ?_
    refine spec_skip ‹_› ?_
    refine spec_instr (Exec.addN ‹_› _ _ _ (by config_simp; omega)) fun hw₃ => ?_
    refine ⟨DkIRx.next hG hI hlt hw₃ ?_ (fun a ha => by config_simp; exact hI.fr a ha)
      (by config_simp; exact hI.r37) (by config_simp; exact hI.r39)
      (by config_simp; exact hI.r41) (by config_simp; rw [h12]) (by config_simp; exact hI.tour)
      (fun x hx => by config_simp; exact hI.leaf x hx) (fun x hx => by config_simp)
      (fun x hx => by config_simp; rw [hw]; simp [hcmp]), ?_⟩
    · exact dkRegs_of ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩
        fun r hr hr' => by config_simp; simp only [upd_apply]; split_ifs <;> first | rfl | omega
    config_simp; rw [h12]
    have hB : (p.oe v - c.nreg 2540) * (13 * lg (2 * p.n) + 20) =
        (p.oe v - (c.nreg 2540 + 1)) * (13 * lg (2 * p.n) + 20) +
          (13 * lg (2 * p.n) + 20) := by
      rw [← Nat.succ_mul]; congr 1; omega
    rw [hB]
    omega

set_option maxHeartbeats 2000000 in
/-- **One round**: the extraction of the node of least key and the relaxation of its arcs. -/
theorem dkRound_exec {p : DkP} (hG : DkG p W) {m₀ : ℕ → ℕ} (hM : DkMem p m₀) (c : Config)
    (hI : DkIM p W m₀ c) (hlt : c.nreg 2537 < c.nreg 2509) :
    ∃ c' k', Exec P W dkRound c c' k' ∧ DkIM p W m₀ c' ∧
      dkPot p c'.nmem + k' + 2 ≤ dkPot p c.nmem := by
  have hc := hI.wb
  have hX := hG.wX
  have hDw := hG.wD
  have hdx := hG.dDX
  have hn := hG.n_pos
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ := hI.regs
  rw [hI.r37, h9] at hlt
  generalize hk : dkT p c.nmem 1 = k at hlt
  -- the descent
  obtain ⟨c₁, k₁, e₁, hw₁, hK₁, hm₁, hl1, hl2, hval, hk₁⟩ :=
    dkDesc_exec (P := P) hG c hc hI.regs hI.tour
  generalize hl : c₁.nreg 2536 = l at hl1 hl2 hval
  have hR₁ := dkRegs_of hI.regs fun r h1 h2 => hK₁ r (Or.inl (by omega))
  obtain ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14⟩ := hR₁
  have hvn : l - p.n < p.n := by omega
  have hleafv := hI.leaf (l - p.n) hvn
  rw [show p.n + (l - p.n) = l by omega, hval, hk] at hleafv
  have hvnot : c.nmem (p.Xb + (l - p.n)) = 0 := by
    rcases hI.done01 _ hvn with h | h
    · exact h
    · rw [h] at hleafv; simp at hleafv; omega
  have hdistv : c.nmem (p.Db + (l - p.n)) = k := by
    rw [hvnot] at hleafv; simp at hleafv
    exact hleafv.symm
  -- marking the node done and removing it from the tree
  obtain ⟨c₂, k₂, e₂, hw₂, hpost⟩ : ∃ c₂ k₂, Exec P W (block [.subN 2539 2536 2500,
      .addN 2547 2502 2539, .storeN 2547 2512, .addN 2547 2503 2536, .storeN 2547 2509,
      .divN 2530 2536 2513]) c₁ c₂ k₂ ∧
      WordsBounded W c₂ ∧ (k₂ = 6 ∧
        (∀ r, r ≠ 2539 → r ≠ 2547 → r ≠ 2530 → c₂.nreg r = c₁.nreg r) ∧
        c₂.nreg 2539 = l - p.n ∧ c₂.nreg 2530 = l / 2 ∧
        c₂.nmem = upd (upd c₁.nmem (p.Xb + (l - p.n)) 1) (p.Xb + p.n + l) p.Inf) := by
    exec_block
    · config_simp; rw [g2, hl, g0]; omega
    · config_simp; rw [g3, hl]; omega
    refine ⟨‹_›, rfl, fun r a b e => ?_, by config_simp; rw [hl, g0], by config_simp; rw [hl, g13],
      by config_simp; rw [hl, g0, g2, g3, g12, g9]⟩
    config_simp; simp only [upd_apply, a, b, e, ite_false]
  obtain ⟨rfl, hK₂, h39₂, h30₂, hm₂⟩ := hpost
  rw [hm₁] at hm₂
  have hexc : IsTourExc p.n (dkT p c₂.nmem) (c₂.nreg 2530) := by
    rw [h30₂]
    exact dk_isTourExc_set hI.tour hl1 fun a ha2 ha => by
      simp only [dkT, hm₂, upd_apply]; split_ifs <;> first | omega | rfl
  have hR₂ := dkRegs_of ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14⟩
    fun r h1 h2 => hK₂ r (by omega) (by omega) (by omega)
  obtain ⟨c₃, k₃, e₃, hw₃, hK₃, hT₃, hf₃, hk₃⟩ := dkUpd_exec (P := P) hG c₂ hw₂ hR₂
    (by rw [h30₂]; omega) hexc
  have hR₃ := dkRegs_of hR₂ fun r h1 h2 => hK₃ r (Or.inl (by omega))
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14⟩ := hR₃
  have h39₃ : c₃.nreg 2539 = l - p.n := (hK₃ 2539 (Or.inr (by omega))).trans h39₂
  -- the arcs of the node
  generalize hv : l - p.n = v at hvn hvnot hdistv h39₂ h39₃ hm₂
  have hmem₃ : ∀ a, (a < p.Xb + p.n + 1 ∨ p.Xb + 2 * p.n ≤ a) → c₃.nmem a =
      if a = p.Xb + p.n + l then p.Inf else if a = p.Xb + v then 1 else c.nmem a := by
    intro a ha; rw [hf₃ a ha, hm₂]; simp only [upd_apply]
  have hrd₃ : ∀ a, ¬ DkOut p a → c₃.nmem a = m₀ a := by
    intro a ha
    have ha' := ha
    unfold DkOut at ha'
    rw [hmem₃ a (by omega)]; split_ifs <;> first | omega | exact hI.fr a ha
  obtain ⟨c₄, k₄, e₄, hw₄, hpost⟩ : ∃ c₄ k₄, Exec P W (block [.addN 2547 2504 2539,
      .loadN 2540 2547, .addN 2547 2505 2539, .loadN 2541 2547]) c₃ c₄ k₄ ∧ WordsBounded W c₄ ∧
      (k₄ = 4 ∧ (∀ r, r ≠ 2547 → r ≠ 2540 → r ≠ 2541 → c₄.nreg r = c₃.nreg r) ∧
        c₄.nreg 2540 = p.ob v ∧ c₄.nreg 2541 = p.oe v ∧ c₄.nmem = c₃.nmem) := by
    exec_block
    · config_simp; rw [h39₃, f4]; exact (hG.aOB v hvn).1
    · config_simp; rw [h39₃, f5]; exact (hG.aOE v hvn).1
    refine ⟨‹_›, rfl, fun r a b e => ?_,
      by config_simp; rw [h39₃, f4, hrd₃ _ (hG.aOB v hvn).2, hM.ob v hvn],
      by config_simp; rw [h39₃, f5, hrd₃ _ (hG.aOE v hvn).2, hM.oe v hvn], by config_simp⟩
    config_simp; simp only [upd_apply, a, b, e, ite_false]
  obtain ⟨rfl, hK₄, h40₄, h41₄, hm₄⟩ := hpost
  have hR₄ := dkRegs_of ⟨f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14⟩
    fun r h1 h2 => hK₄ r (by omega) (by omega) (by omega)
  -- the memory after the extraction
  have hmem : ∀ a, (a < p.Xb + p.n + 1 ∨ p.Xb + 2 * p.n ≤ a) → c₄.nmem a =
      if a = p.Xb + p.n + l then p.Inf else if a = p.Xb + v then 1 else c.nmem a := by
    intro a ha; rw [hm₄]; exact hmem₃ a ha
  have hdist : ∀ x < p.n, c₄.nmem (p.Db + x) = c.nmem (p.Db + x) := by
    intro x hx; rw [hmem _ (by omega)]; split_ifs <;> first | rfl | omega
  have hdn : ∀ x < p.n, c₄.nmem (p.Xb + x) = if x = v then 1 else c.nmem (p.Xb + x) := by
    intro x hx; rw [hmem _ (by omega)]; split_ifs <;> first | rfl | omega
  obtain ⟨k₀, hk₀1, hk₀2⟩ := hI.key
  have hkv : k₀ ≤ k := by rw [← hdistv]; exact hk₀2 v hvn hvnot
  have hIR : DkIRx p W m₀ v k (fun x => if x = v then 1 else c.nmem (p.Xb + x)) c₄ := by
    refine ⟨hw₄, hR₄, fun a ha => by rw [hm₄]; exact hrd₃ a ha, ?_, ?_, h41₄, by rw [h40₄],
      by rw [h40₄]; exact hG.ob_le v hvn, hvn, by rw [hm₄]; exact hT₃, fun x hx => ?_,
      hdn, by simp, fun x hx => ?_, fun x hx => by rw [hdist x hx]; exact hI.dle x hx,
      by rw [hdist v hvn]; exact hdistv, hlt, fun x hx h => ?_, fun x hx h => ?_,
      fun u hu hDu huv j h1 h2 => ?_, fun j h1 h2 => by rw [h40₄] at h2; omega,
      fun x hx h => by rw [hdist x hx] at h ⊢; exact hI.reach x hx h,
      by rw [hdist _ hG.s_lt]; exact hI.srcz⟩
    · rw [hK₄ 2537 (by omega) (by omega) (by omega), hK₃ 2537 (Or.inr (by omega)),
        hK₂ 2537 (by omega) (by omega) (by omega), hK₁ 2537 (Or.inr (by omega)), hI.r37, hk]
    · rw [hK₄ 2539 (by omega) (by omega) (by omega), h39₃]
    · simp only [dkT]; rw [hmem _ (by omega), hdn x hx, hdist x hx]
      by_cases hxv : x = v
      · subst hxv; simp only [show p.Xb + p.n + (p.n + x) = p.Xb + p.n + l by omega, ite_true]
      · have := hI.leaf x hx; simp only [dkT] at this
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
      have h1 := root_le hI.tour (l := p.n + x) (by omega) (by omega)
      have h2 := hI.leaf x hx
      rw [h] at h2
      rw [hk] at h1
      simp at h2
      simp only [dkT] at h1 h2
      omega
    · simp only [huv, ite_false] at hDu
      rw [hdist u hu, hdist _ (hG.nh_lt u hu j h1 h2)]
      exact hI.relaxed u hu hDu j h1 h2
  -- the relaxations
  obtain ⟨c₅, k₅, e₅, hI₅, hn₅, hk₅⟩ := Exec.whileLtN_potential (P := P) (W := W) (a := 2540)
    (b := 2541) (body := dkRelax)
    (DkIRx p W m₀ v k (fun x => if x = v then 1 else c.nmem (p.Xb + x)))
    (fun c => (p.oe v - c.nreg 2540) * (13 * lg (2 * p.n) + 20)) (fun c h => h.wb)
    (fun c hc hlt => dkRelax_exec hG hM c hc hlt) hIR
  have h40₅ : c₅.nreg 2540 = p.oe v := by
    have := hI₅.r40hi; rw [hI₅.r41] at hn₅; omega
  obtain ⟨i0, i1, i2, i3, i4, i5, i6, i7, i8, i9, i10, i11, i12, i13, i14⟩ := hI₅.regs
  have hc₅ := hI₅.wb
  obtain ⟨c₆, k₆, e₆, hw₆, hpost⟩ : ∃ c₆ k₆, Exec P W (block [.addN 2547 2503 2512,
      .loadN 2537 2547]) c₅ c₆ k₆ ∧ WordsBounded W c₆ ∧
      (k₆ = 2 ∧ (∀ r, r ≠ 2547 → r ≠ 2537 → c₆.nreg r = c₅.nreg r) ∧
        c₆.nreg 2537 = dkT p c₅.nmem 1 ∧ c₆.nmem = c₅.nmem) := by
    exec_block
    · config_simp; rw [i3, i12]; omega
    refine ⟨‹_›, rfl, fun r a b => ?_, by config_simp; rw [i3, i12]; rfl, by config_simp⟩
    config_simp; simp only [upd_apply, a, b, ite_false]
  obtain ⟨rfl, hK₆, h37₆, hm₆⟩ := hpost
  refine ⟨c₆, _, .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ (.seq e₅ e₆)))), ⟨hw₆,
    dkRegs_of ⟨i0, i1, i2, i3, i4, i5, i6, i7, i8, i9, i10, i11, i12, i13, i14⟩
      fun r h1 h2 => hK₆ r (by omega) (by omega),
    fun a ha => by rw [hm₆]; exact hI₅.fr a ha,
    by rw [hm₆]; exact hI₅.tour, by rw [hm₆]; exact hI₅.leaf,
    fun x hx => by rw [hm₆, hI₅.dn x hx]; exact hI₅.done01 x hx,
    by rw [hm₆]; exact hI₅.dle, ⟨k, fun x hx h => ?_, fun x hx h => ?_⟩,
    fun u hu hDu j h1 h2 => ?_, by rw [hm₆]; exact hI₅.reach, by rw [hm₆]; exact hI₅.srcz,
    by rw [h37₆, hm₆]⟩, ?_⟩
  · rw [hm₆, hI₅.dn x hx] at h; rw [hm₆]; exact hI₅.kdone x hx h
  · rw [hm₆, hI₅.dn x hx] at h; rw [hm₆]; exact hI₅.knot x hx h
  · rw [hm₆] at hDu ⊢; rw [hI₅.dn u hu] at hDu
    by_cases huv : u = v
    · subst huv; rw [hI₅.distv]; exact hI₅.relv j h1 (by rw [h40₅]; exact h2)
    · simp only [huv, ite_false] at hDu
      exact hI₅.relaxed u hu (by simp only [huv, ite_false]; exact hDu) huv j h1 h2
  · -- the cost
    have hpot := dkPot_step (p := p) (m := c.nmem) (m' := c₆.nmem) hvn hvnot
      (by rw [hm₆, hI₅.dn v hvn]; simp)
      (fun x hx hxv => by rw [hm₆, hI₅.dn x hx]; simp [hxv])
    have hL1 : lg (c₂.nreg 2530) ≤ lg (2 * p.n) := lg_mono (by rw [h30₂]; omega)
    beta_reduce at hk₅
    rw [h40₄] at hk₅
    have : (p.oe v - p.ob v) * (13 * lg (2 * p.n) + 20) =
        (13 * lg (2 * p.n) + 20) * (p.oe v - p.ob v) := Nat.mul_comm _ _
    omega

end NegSSSP

end PlanarFlow
