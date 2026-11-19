module

public import PlanarFlow.BKMNW.NrKahnRun

/-!
# Kahn's algorithm on the machine: the main loop

The scratch of `kahnP` from `S`: `POS [S, S+m)`, `IND [S+m, S+2m)`, `Q [S+2m, S+3m)`, `OB`, `OE`,
`OL` at `S+5m+1`, `S+6m+1`, `S+7m+1`. With the memory `mb` outside `IND` and `Q` fixed (`KCtx`):

* `KIn.congr`, `KSt.congr`, `kQ_len_le`, `nrF_sum_le`;
* `kNL_exec` (the positive darts of the popped vertex), **`kML_exec`** (the main loop, from the
  state `KSt … 0 t` of the scan to `KSt … t' t'`).
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace PlanarFlow

namespace BKMNW

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs NegSSSP

variable {m : ℕ} {vl tl hd ps : ℕ → ℕ}

lemma KIn.congr {Q IND Q' IND' : ℕ → ℕ} {h t s : ℕ} (hk : KIn m vl tl hd ps Q IND h t s)
    (hQ : ∀ k < t, Q' k = Q k) (hI : ∀ w < m, IND' w = IND w) :
    KIn m vl tl hd ps Q' IND' h t s := by
  have hkq : ∀ t', t' ≤ t → kQ Q' t' = kQ Q t' := fun t' ht' => by
    simp only [kQ]; exact List.map_congr_left fun k hk' => hQ k (by have := List.mem_range.1 hk'; omega)
  have hh := hk.ht
  refine ⟨hk.ht, by rw [hkq t le_rfl]; exact hk.nd, fun k hk' => by rw [hQ k hk']; exact hk.rep k hk',
    fun w hw => ?_, fun w hw => ?_, fun k hk' j hj hp he => ?_⟩
  · rw [hI w hw.1, hQ h hh, hkq h hh.le]; exact hk.ind w hw
  · rw [hI w hw.1, hkq t le_rfl]; exact hk.mem w hw
  · rw [hQ k hk'] at he
    obtain ⟨k', hk'', e⟩ := hk.topo k hk' j hj hp he
    exact ⟨k', hk'', by rw [hQ k' (by omega)]; exact e⟩

lemma KSt.congr {Q IND Q' IND' : ℕ → ℕ} {h t : ℕ} (hk : KSt m vl tl hd ps Q IND h t)
    (hQ : ∀ k < t, Q' k = Q k) (hI : ∀ w < m, IND' w = IND w) :
    KSt m vl tl hd ps Q' IND' h t := by
  have hkq : ∀ t', t' ≤ t → kQ Q' t' = kQ Q t' := fun t' ht' => by
    simp only [kQ]; exact List.map_congr_left fun k hk' => hQ k (by have := List.mem_range.1 hk'; omega)
  have hh := hk.ht
  refine ⟨hk.ht, by rw [hkq t le_rfl]; exact hk.nd, fun k hk' => by rw [hQ k hk']; exact hk.rep k hk',
    fun w hw => ?_, fun w hw => ?_, fun k hk' j hj hp he => ?_⟩
  · rw [hI w hw.1, hkq h hh]; exact hk.ind w hw
  · rw [hI w hw.1, hkq t le_rfl]; exact hk.mem w hw
  · rw [hQ k hk'] at he
    obtain ⟨k', hk'', e⟩ := hk.topo k hk' j hj hp he
    exact ⟨k', hk'', by rw [hQ k' (by omega)]; exact e⟩

/-- A queue of distinct vertices has at most `m` entries. -/
lemma kQ_len_le {Q : ℕ → ℕ} {t : ℕ} (hnd : (kQ Q t).Nodup) (hlt : ∀ k < t, Q k < m) : t ≤ m := by
  have h1 : (kQ Q t).toFinset ⊆ range m := fun x hx => by
    obtain ⟨k, hk, rfl⟩ := mem_kQ.1 (List.mem_toFinset.1 hx)
    exact mem_range.2 (hlt k hk)
  have := card_le_card h1
  rw [List.toFinset_card_of_nodup hnd, card_range] at this
  simpa [kQ] using this

lemma nrF_len (u : ℕ) :
    (nrF tl ps m u).length = ((range m).filter fun j => ps j ≠ 0 ∧ tl j = u).card := by
  rw [← List.toFinset_card_of_nodup (nrF_nodup u)]
  congr 1; ext j
  simp [nrF]

/-- The positive darts of distinct vertices are at most `m`. -/
lemma nrF_sum_eq : ∀ (q : List ℕ), q.Nodup →
    (q.map fun u => (nrF tl ps m u).length).sum =
      ((range m).filter fun j => ps j ≠ 0 ∧ tl j ∈ q).card
  | [], _ => by simp
  | a :: q, hq => by
    obtain ⟨ha, hq'⟩ := List.nodup_cons.1 hq
    rw [List.map_cons, List.sum_cons, nrF_sum_eq q hq', nrF_len, ← card_union_of_disjoint]
    · congr 1; ext j; simp only [mem_union, mem_filter, mem_range, List.mem_cons]; tauto
    · rw [disjoint_filter]; intro j _ h1 h2; exact ha (h1.2 ▸ h2.2)

lemma nrF_sum_le (q : List ℕ) (hq : q.Nodup) :
    (q.map fun u => (nrF tl ps m u).length).sum ≤ m := by
  rw [nrF_sum_eq q hq]; exact (card_filter_le _ _).trans (by simp)

/-- **The context of the main loop**: the memory `mb` outside `IND` and `Q`. -/
structure KCtx (mb : ℕ → ℕ) (m S VL RV W : ℕ) : Prop where
  hO : ∀ y < m, mb (S + 6 * m + 1 + y) = mb (S + 5 * m + 1 + y) +
      (nrF (fun v => mb (VL + v)) (fun i => mb (S + i)) m y).length ∧
    mb (S + 6 * m + 1 + y) ≤ m ∧
    ∀ t (ht : t < (nrF (fun v => mb (VL + v)) (fun i => mb (S + i)) m y).length),
      mb (S + 7 * m + 1 + (mb (S + 5 * m + 1 + y) + t)) =
        (nrF (fun v => mb (VL + v)) (fun i => mb (S + i)) m y)[t]
  rv : ∀ j < m, mb (RV + j) < m
  vlt : ∀ j < m, mb (VL + j) < m ∧ mb (VL + mb (VL + j)) = mb (VL + j)
  dV : NrSep VL m S (8 * m + 1)
  dR : NrSep RV m S (8 * m + 1)
  wS : S + 8 * m + 1 ≤ W
  wV : VL + m ≤ W
  wR : RV + m ≤ W

variable {P : Input} {W : ℕ}

set_option maxHeartbeats 1000000 in
/-- **The positive darts of the popped vertex `u = Q[h]`.** -/
theorem kNL_exec (c : Config) (hc : WordsBounded W c) {mb : ℕ → ℕ} {m S VL RV : ℕ}
    (hK : KCtx mb m S VL RV W) {h t u : ℕ}
    (hfr : ∀ a, (a < S + m ∨ S + 3 * m ≤ a) → c.nmem a = mb a)
    (r1 : c.nreg 9101 = VL) (r2 : c.nreg 9102 = RV) (r6 : c.nreg 9106 = 1)
    (r7 : c.nreg 9107 = 0) (r8 : c.nreg 9108 = S + m) (r9 : c.nreg 9109 = S + 2 * m)
    (r14 : c.nreg 9114 = S + 7 * m + 1) (r20 : c.nreg 9120 = t)
    (r23 : c.nreg 9123 = mb (S + 5 * m + 1 + u)) (r24 : c.nreg 9124 = mb (S + 6 * m + 1 + u))
    (hu : c.nmem (S + 2 * m + h) = u) (hum : u < m)
    (hk : KIn m (fun v => mb (VL + v)) (fun v => mb (VL + v)) (fun j => mb (VL + mb (RV + j)))
      (fun i => mb (S + i)) (fun k => c.nmem (S + 2 * m + k)) (fun w => c.nmem (S + m + w)) h t 0) :
    ∃ c' t₁, Exec P W (.whileLtN 9123 9124 kN) c c' t₁ ∧
      t₁ ≤ 18 * (nrF (fun v => mb (VL + v)) (fun i => mb (S + i)) m u).length + 2 ∧
      ∃ t', c'.nreg 9120 = t' ∧ t ≤ t' ∧ (∀ k < t, c'.nmem (S + 2 * m + k) = c.nmem (S + 2 * m + k)) ∧
        KIn m (fun v => mb (VL + v)) (fun v => mb (VL + v)) (fun j => mb (VL + mb (RV + j)))
          (fun i => mb (S + i)) (fun k => c'.nmem (S + 2 * m + k)) (fun w => c'.nmem (S + m + w))
          h t' (nrF (fun v => mb (VL + v)) (fun i => mb (S + i)) m u).length ∧
        (∀ a, (a < S + m ∨ S + 3 * m ≤ a) → c'.nmem a = mb a) ∧
        (∀ x, x ≠ 9116 → x ≠ 9118 → x ≠ 9120 → x ≠ 9123 → (x < 9125 ∨ 9127 < x) →
          c'.nreg x = c.nreg x) ∧
        c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have wS := hK.wS
  have wV := hK.wV
  have wR := hK.wR
  obtain ⟨hOE, hOEm, hOL⟩ := hK.hO u hum
  set L := nrF (fun v => mb (VL + v)) (fun i => mb (S + i)) m u with hL
  set lo := mb (S + 5 * m + 1 + u) with hlo
  let J : ℕ → Config → Prop := fun k c' =>
    (∀ x, x ≠ 9116 → x ≠ 9118 → x ≠ 9120 → x ≠ 9123 → (x < 9125 ∨ 9127 < x) →
      c'.nreg x = c.nreg x) ∧
    (∃ t', c'.nreg 9120 = t' ∧ c'.nmem (S + 2 * m + h) = u ∧ t ≤ t' ∧
      (∀ k < t, c'.nmem (S + 2 * m + k) = c.nmem (S + 2 * m + k)) ∧
      KIn m (fun v => mb (VL + v)) (fun v => mb (VL + v)) (fun j => mb (VL + mb (RV + j)))
        (fun i => mb (S + i)) (fun k => c'.nmem (S + 2 * m + k)) (fun w => c'.nmem (S + m + w))
        h t' (k - lo)) ∧
    (∀ a, (a < S + m ∨ S + 3 * m ≤ a) → c'.nmem a = mb a) ∧
    c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output
  obtain ⟨c', t₁, ex, ht₁, -, -, j1, ⟨t', j2, -, jt, jq, j3⟩, j4, j5, j6, j7⟩ := lnRange (P := P)
    (a := 9123) (b := 9124) (body := kN) J (B := 16) c hc r23 (by rw [r24, hOE]) (by omega)
    ⟨fun _ _ _ _ _ _ => rfl, ⟨t, r20, hu, le_rfl, fun _ _ => rfl, by simpa using hk⟩, hfr, rfl, rfl, rfl⟩
    (fun k c₁ hlo' hi hw h23 h24 ⟨f₁, ⟨t₁, g20, gu, gt, gq, gk⟩, o₁, q1, q2, q3⟩ => by
      have hs : k - lo < L.length := by omega
      have hht := gk.ht
      have htm : t₁ ≤ m := kQ_len_le gk.nd fun k hk' => (gk.rep k hk').1
      -- the dart
      have hj : c₁.nmem (S + 7 * m + 1 + k) = L[k - lo] := by
        have := hOL (k - lo) hs
        rw [show lo + (k - lo) = k by omega] at this
        rw [o₁ _ (by omega)]; exact this
      have hjm : L[k - lo] < m := (nrF_mem (List.getElem_mem hs)).1
      have hrv := hK.rv _ hjm
      obtain ⟨hwm, hwr⟩ := hK.vlt _ hrv
      have eR : c₁.nmem (RV + L[k - lo]) = mb (RV + L[k - lo]) :=
        o₁ _ (by have := hK.dR; rcases this with h | h <;> omega)
      have eV : c₁.nmem (VL + mb (RV + L[k - lo])) = mb (VL + mb (RV + L[k - lo])) :=
        o₁ _ (by have := hK.dV; rcases this with h | h <;> omega)
      set w := mb (VL + mb (RV + L[k - lo])) with hw'
      obtain ⟨c₂, t₂, e₂, ht₂, g23, gif, gn, gr, grm, go⟩ := kN_exec (P := P) c₁ hw
        (OLb := S + 7 * m + 1) (RV := RV) (VL := VL) (A := S + m) (Qb := S + 2 * m) (k := k)
        (t := t₁) (by rw [f₁ _ (by omega) (by omega) (by omega) (by omega) (by omega), r14]) h23
        (by rw [f₁ _ (by omega) (by omega) (by omega) (by omega) (by omega), r2])
        (by rw [f₁ _ (by omega) (by omega) (by omega) (by omega) (by omega), r1])
        (by rw [f₁ _ (by omega) (by omega) (by omega) (by omega) (by omega), r8])
        (by rw [f₁ _ (by omega) (by omega) (by omega) (by omega) (by omega), r6])
        (by rw [f₁ _ (by omega) (by omega) (by omega) (by omega) (by omega), r7])
        (by rw [f₁ _ (by omega) (by omega) (by omega) (by omega) (by omega), r9]) g20
        (by omega) (by rw [hj]; omega) (by rw [hj, eR]; omega) (by rw [hj, eR, eV]; omega)
        (by omega) (by omega)
      rw [hj, eR, eV] at gif
      have hQh : (fun k => c₁.nmem (S + 2 * m + k)) h = u := gu
      have hkin := kin_step (m := m) (vl := fun v => mb (VL + v)) (tl := fun v => mb (VL + v))
        (hd := fun j => mb (VL + mb (RV + j))) (ps := fun i => mb (S + i)) gk
        (s := k - lo) (by simpa only [hQh] using hs)
        (fun j hj' => ⟨(hK.vlt _ (hK.rv j hj')).1, (hK.vlt _ (hK.rv j hj')).2⟩)
        (j := L[k - lo]) (w := w) (by simp only [hQh]; rfl) rfl
      have hsk : k - lo + 1 = k + 1 - lo := by omega
      rw [hsk] at hkin
      refine ⟨c₂, t₂, e₂, ht₂, g23, by rw [gn _ (by omega) (by omega) (by omega) (by omega) (by omega)]; exact h24,
        fun x h1 h2 h3 h4 h5 => by rw [gn x h1 h2 h3 h4 h5, f₁ x h1 h2 h3 h4 h5], ?_, ?_,
        by rw [gr, q1], by rw [grm, q2], by rw [go, q3]⟩
      · split_ifs at gif with hx
        · obtain ⟨g20', gm⟩ := gif
          have hx' : c₁.nmem (S + m + w) - 1 ≠ 0 := by omega
          refine ⟨t₁, g20', by rw [gm, upd_other _ _ _ (by omega)]; exact gu, gt,
            fun k' hk' => by rw [gm, upd_other _ _ _ (by omega)]; exact gq k' hk', ?_⟩
          refine (hkin.2 hx').congr (fun k' hk' => ?_) (fun w' hw'' => ?_)
          · beta_reduce; rw [gm, upd_other _ _ _ (by omega)]
          · beta_reduce
            rw [gm]
            by_cases e : w' = w
            · subst e; rw [upd_same, Function.update_self]
            · rw [upd_other _ _ _ (by omega), Function.update_of_ne e]
        · obtain ⟨g20', gm⟩ := gif
          have hx' : c₁.nmem (S + m + w) - 1 = 0 := by omega
          have hk1 := hkin.1 hx'
          have htm' : t₁ + 1 ≤ m := kQ_len_le hk1.nd fun k hk' => (hk1.rep k hk').1
          refine ⟨t₁ + 1, g20', by rw [gm, upd_other _ _ _ (by omega), upd_other _ _ _ (by omega)]; exact gu,
            by omega, fun k' hk' => by
              rw [gm, upd_other _ _ _ (by omega), upd_other _ _ _ (by omega)]; exact gq k' hk', ?_⟩
          refine hk1.congr (fun k' hk' => ?_) (fun w' hw'' => ?_)
          · beta_reduce
            rw [gm]
            by_cases e : k' = t₁
            · subst e; rw [upd_same, Function.update_self]
            · rw [upd_other _ _ _ (by omega), upd_other _ _ _ (by omega), Function.update_of_ne e]
          · beta_reduce
            rw [gm, upd_other _ _ _ (by omega)]
            by_cases e : w' = w
            · subst e; rw [upd_same, Function.update_self]
            · rw [upd_other _ _ _ (by omega), Function.update_of_ne e]
      · intro a ha
        split_ifs at gif with hx
        · rw [gif.2, upd_other _ _ _ (by omega)]; exact o₁ a ha
        · have hk1 := hkin.1 (by omega)
          have htm' : t₁ + 1 ≤ m := kQ_len_le hk1.nd fun k hk' => (hk1.rep k hk').1
          rw [gif.2, upd_other _ _ _ (by omega), upd_other _ _ _ (by omega)]; exact o₁ a ha)
  refine ⟨c', t₁, ex, by omega, t', j2, jt, jq, by simpa [show lo + L.length - lo = L.length by omega]
    using j3, j4, j1, j5, j6, j7⟩

/-- The degrees of the popped vertices. -/
def kDeg (mb : ℕ → ℕ) (m S VL : ℕ) (Q : ℕ → ℕ) (h : ℕ) : ℕ :=
  ((kQ Q h).map fun u => (nrF (fun v => mb (VL + v)) (fun i => mb (S + i)) m u).length).sum

set_option maxHeartbeats 1000000 in
/-- **The main loop of Kahn's algorithm.** -/
theorem kML_exec (c : Config) (hc : WordsBounded W c) {mb : ℕ → ℕ} {m S VL RV : ℕ}
    (hK : KCtx mb m S VL RV W) {t : ℕ}
    (hfr : ∀ a, (a < S + m ∨ S + 3 * m ≤ a) → c.nmem a = mb a)
    (r1 : c.nreg 9101 = VL) (r2 : c.nreg 9102 = RV) (r6 : c.nreg 9106 = 1)
    (r7 : c.nreg 9107 = 0) (r8 : c.nreg 9108 = S + m) (r9 : c.nreg 9109 = S + 2 * m)
    (r12 : c.nreg 9112 = S + 5 * m + 1) (r13 : c.nreg 9113 = S + 6 * m + 1)
    (r14 : c.nreg 9114 = S + 7 * m + 1) (r20 : c.nreg 9120 = t) (r21 : c.nreg 9121 = 0)
    (hs : KSt m (fun v => mb (VL + v)) (fun v => mb (VL + v)) (fun j => mb (VL + mb (RV + j)))
      (fun i => mb (S + i)) (fun k => c.nmem (S + 2 * m + k)) (fun w => c.nmem (S + m + w)) 0 t) :
    ∃ c' t₁, Exec P W (.whileLtN 9121 9120 kM) c c' t₁ ∧ t₁ ≤ 31 * m + 2 ∧
      ∃ t', c'.nreg 9120 = t' ∧
        KSt m (fun v => mb (VL + v)) (fun v => mb (VL + v)) (fun j => mb (VL + mb (RV + j)))
          (fun i => mb (S + i)) (fun k => c'.nmem (S + 2 * m + k)) (fun w => c'.nmem (S + m + w))
          t' t' ∧
        (∀ a, (a < S + m ∨ S + 3 * m ≤ a) → c'.nmem a = mb a) ∧
        (∀ x, (x < 9116 ∨ 9127 < x) → c'.nreg x = c.nreg x) ∧
        c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have wS := hK.wS
  let I : Config → Prop := fun c' => WordsBounded W c' ∧
    (∀ x, (x < 9116 ∨ 9127 < x) → c'.nreg x = c.nreg x) ∧
    (∃ h t', c'.nreg 9121 = h ∧ c'.nreg 9120 = t' ∧
      KSt m (fun v => mb (VL + v)) (fun v => mb (VL + v)) (fun j => mb (VL + mb (RV + j)))
        (fun i => mb (S + i)) (fun k => c'.nmem (S + 2 * m + k)) (fun w => c'.nmem (S + m + w))
        h t') ∧
    (∀ a, (a < S + m ∨ S + 3 * m ≤ a) → c'.nmem a = mb a) ∧
    c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output
  let Φ : Config → ℕ := fun c' => 13 * (m - c'.nreg 9121) +
    18 * (m - kDeg mb m S VL (fun k => c'.nmem (S + 2 * m + k)) (c'.nreg 9121))
  have hI0 : I c := ⟨hc, fun _ _ => rfl, ⟨0, t, r21, r20, hs⟩, hfr, rfl, rfl, rfl⟩
  obtain ⟨c', t₁, ex, ⟨hw', f', ⟨h', t', g21, g20, hst⟩, o', q1, q2, q3⟩, hn, ht₁⟩ :=
    Exec.whileLtN_potential (P := P) (W := W) (a := 9121) (b := 9120) (body := kM) I Φ
      (fun c h => h.1) (fun c₀ ⟨hw, f₀, ⟨h, t₀, g21, g20, hk⟩, o₀, q1, q2, q3⟩ hlt => by
        rw [g21, g20] at hlt
        have htm : t₀ ≤ m := kQ_len_le hk.nd fun k hk' => (hk.rep k hk').1
        obtain ⟨hum, -⟩ := hk.rep h hlt
        set u := c₀.nmem (S + 2 * m + h) with hu
        obtain ⟨hOE, hOEm, -⟩ := hK.hO u hum
        obtain ⟨c₁, t₂, e₁, ht₂, a22, a21, a23, a24, f₁, m₁, rr₁, rm₁, o₁⟩ := kM1_exec (P := P) c₀ hw
          (Qb := S + 2 * m) (OBb := S + 5 * m + 1) (OEb := S + 6 * m + 1) (h := h)
          (by rw [f₀ _ (by omega), r9]) (by rw [f₀ _ (by omega), r12])
          (by rw [f₀ _ (by omega), r13]) g21 (by rw [f₀ _ (by omega), r6]) (by omega)
          (by omega) (by omega) (by omega)
        rw [o₀ _ (by omega)] at a23 a24
        have k1 : ∀ x, (x < 9116 ∨ 9127 < x) → c₁.nreg x = c.nreg x := fun x hx => by
          rw [f₁ x (by omega) (by omega), f₀ x hx]
        obtain ⟨c₂, t₃, e₂, ht₃, t'', g20', gt, gq, gk, o₂, f₂, rr₂, rm₂, oo₂⟩ := kNL_exec (P := P) c₁
          e₁.wb_right hK (h := h) (t := t₀) (u := u) (fun a ha => by rw [m₁]; exact o₀ a ha)
          (by rw [k1 _ (by omega), r1]) (by rw [k1 _ (by omega), r2]) (by rw [k1 _ (by omega), r6])
          (by rw [k1 _ (by omega), r7]) (by rw [k1 _ (by omega), r8]) (by rw [k1 _ (by omega), r9])
          (by rw [k1 _ (by omega), r14]) (by rw [f₁ _ (by omega) (by omega), g20]) a23 a24
          (by rw [m₁]) hum (by
            have := kin_start hk hlt
            exact this.congr (fun k _ => by beta_reduce; rw [m₁]) (fun w _ => by beta_reduce; rw [m₁]))
        have h21 : c₂.nreg 9121 = h + 1 := by
          rw [f₂ _ (by omega) (by omega) (by omega) (by omega) (by omega), a21]
        have hQ : ∀ k ≤ h, c₂.nmem (S + 2 * m + k) = c₀.nmem (S + 2 * m + k) := fun k hk' => by
          rw [gq k (by omega), m₁]
        have hQh' : c₂.nmem (S + 2 * m + h) = u := hQ h le_rfl
        have hQh : (fun k => c₂.nmem (S + 2 * m + k)) h = u := hQh'
        have hst := kin_close (m := m) (vl := fun v => mb (VL + v)) (tl := fun v => mb (VL + v))
          (hd := fun j => mb (VL + mb (RV + j))) (ps := fun i => mb (S + i))
          (Q := fun k => c₂.nmem (S + 2 * m + k)) (IND := fun w => c₂.nmem (S + m + w))
          (h := h) (t := t'') (by beta_reduce; rw [hQh']; exact gk)
        refine ⟨c₂, t₂ + t₃, .seq e₁ e₂, ⟨e₂.wb_right, fun x hx => ?_, ⟨h + 1, t'', h21, g20', ?_⟩,
          o₂, by rw [rr₂, rr₁, q1], by rw [rm₂, rm₁, q2], by rw [oo₂, o₁, q3]⟩, ?_⟩
        · rw [f₂ x (by omega) (by omega) (by omega) (by omega) (by omega), k1 x hx]
        · exact hst
        · -- the potential
          have hnd : (kQ (fun k => c₂.nmem (S + 2 * m + k)) (h + 1)).Nodup :=
            hst.nd.sublist (by simp only [kQ]; exact ((List.range_sublist).2 hst.ht).map _)
          have hsum := nrF_sum_le (m := m) (tl := fun v => mb (VL + v)) (ps := fun i => mb (S + i)) _ hnd
          have hk1 : kDeg mb m S VL (fun k => c₂.nmem (S + 2 * m + k)) (h + 1) =
              kDeg mb m S VL (fun k => c₀.nmem (S + 2 * m + k)) h +
                (nrF (fun v => mb (VL + v)) (fun i => mb (S + i)) m u).length := by
            have hkq : kQ (fun k => c₂.nmem (S + 2 * m + k)) h =
                kQ (fun k => c₀.nmem (S + 2 * m + k)) h := by
              simp only [kQ]
              exact List.map_congr_left fun k hk' => hQ k (by have := List.mem_range.1 hk'; omega)
            unfold kDeg
            rw [kQ_succ, List.map_append, List.sum_append, hkq]
            simp [hQh']
          have hk2 : kDeg mb m S VL (fun k => c₂.nmem (S + 2 * m + k)) (h + 1) ≤ m := hsum
          show 13 * (m - c₂.nreg 9121) + 18 * (m - kDeg mb m S VL _ (c₂.nreg 9121)) +
              (t₂ + t₃) + 2 ≤ 13 * (m - c₀.nreg 9121) + 18 * (m - kDeg mb m S VL _ (c₀.nreg 9121))
          rw [h21, g21, hk1] at *
          rw [hk1] at hk2
          omega) hI0
  rw [g21, g20] at hn
  have hht := hst.ht
  have e : h' = t' := by omega
  subst e
  refine ⟨c', t₁, ex, ?_, h', g20, hst, o', f', q1, q2, q3⟩
  show t₁ ≤ 31 * m + 2
  have : Φ c = 13 * m + 18 * m := by
    show 13 * (m - c.nreg 9121) + 18 * (m - kDeg mb m S VL _ (c.nreg 9121)) = _
    rw [r21]; simp [kDeg, kQ]
  omega

end BKMNW

end PlanarFlow
