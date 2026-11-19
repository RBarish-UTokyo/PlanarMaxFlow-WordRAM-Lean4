module

public import PlanarFlow.BKMNW.NrKahnMain

/-!
# Kahn's algorithm on the machine: the whole run

**`kahnP_exec`**: from the arrays `VL` (labels, `VL[VL[j]] = VL[j] ≤ j`), `RV`, `G` (`m ≥ 1`
darts), within `kahnCost m = 130 m + 60` steps, the queue `Q = [S + 2m, …)` and `IND` meet
`KSt … t t` for the labels `VL`, the heads `VL[RV[j]]` and the flags `POS[j] = [Z < G[j]]`
(`POS` at `S`); memory changed only in `[S, S + 8m + 1)`.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace PlanarFlow

namespace BKMNW

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs NegSSSP

variable {P : Input} {W : ℕ}

/-- The step bound of `kahnP`. -/
def kahnCost (m : ℕ) : ℕ := 130 * m + 60

/-- `KSt` depends on the labels, heads and flags only below `m`. -/
lemma KSt.congrF {m : ℕ} {vl tl hd ps vl' tl' hd' ps' Q IND : ℕ → ℕ} {h t : ℕ}
    (hk : KSt m vl tl hd ps Q IND h t) (hv : ∀ v < m, vl' v = vl v)
    (htl : ∀ j < m, tl' j = tl j) (hh : ∀ j < m, hd' j = hd j) (hp : ∀ j < m, ps' j = ps j) :
    KSt m vl' tl' hd' ps' Q IND h t := by
  have hr : ∀ w, KRep m vl' w ↔ KRep m vl w := fun w => by
    unfold KRep; constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, by rw [← hv w h1]; exact h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, by rw [hv w h1]; exact h2⟩
  have hkin : ∀ P w, kIn m tl' hd' ps' P w = kIn m tl hd ps P w := fun P w => by
    unfold kIn; congr 1
    exact filter_congr fun j hj => by
      have := mem_range.1 hj; rw [htl j this, hh j this, hp j this]
  refine ⟨hk.ht, hk.nd, fun k hk' => (hr _).2 (hk.rep k hk'), fun w hw => ?_,
    fun w hw => hk.mem w ((hr w).1 hw), fun k hk' j hj hp' he => ?_⟩
  · rw [hkin]; exact hk.ind w ((hr w).1 hw)
  · rw [hp j hj] at hp'; rw [hh j hj] at he
    obtain ⟨k', h1, h2⟩ := hk.topo k hk' j hj hp' he
    exact ⟨k', h1, by rw [htl j hj]; exact h2⟩

set_option maxHeartbeats 4000000 in
/-- **Kahn's algorithm on the machine** (see the module docstring). -/
theorem kahnP_exec (c : Config) (hc : WordsBounded W c) {m VL RV G Z S : ℕ}
    (r0 : c.nreg 9100 = m) (r1 : c.nreg 9101 = VL) (r2 : c.nreg 9102 = RV)
    (r3 : c.nreg 9103 = G) (r4 : c.nreg 9104 = Z) (r5 : c.nreg 9105 = S) (hm : 0 < m)
    (hRV : ∀ j < m, c.nmem (RV + j) < m)
    (hVL : ∀ j < m, c.nmem (VL + j) < m ∧ c.nmem (VL + c.nmem (VL + j)) = c.nmem (VL + j) ∧
      c.nmem (VL + j) ≤ j)
    (dV : NrSep VL m S (8 * m + 1)) (dR : NrSep RV m S (8 * m + 1))
    (dG : NrSep G m S (8 * m + 1)) (wS : S + 8 * m + 1 ≤ W) (wV : VL + m ≤ W)
    (wR : RV + m ≤ W) (wG : G + m ≤ W) :
    ∃ c' t₁, Exec P W kahnP c c' t₁ ∧ t₁ ≤ kahnCost m ∧
      (∀ i < m, c'.nmem (S + i) = kps c.nmem G Z i) ∧
      ∃ t', KSt m (fun v => c.nmem (VL + v)) (fun v => c.nmem (VL + v))
        (fun j => c.nmem (VL + c.nmem (RV + j))) (fun i => c'.nmem (S + i))
        (fun k => c'.nmem (S + 2 * m + k)) (fun w => c'.nmem (S + m + w)) t' t' ∧
      (∀ a, (a < S ∨ S + 8 * m + 1 ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ x, x < 1500 ∨ (1520 < x ∧ x < 9106) ∨ 9127 < x → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  -- the bases
  obtain ⟨c₁, t₁, e₁, ht₁, a6, a7, a8, a9, a10, a11, a12, a13, a14, f₁, m₁, rr₁, rm₁, o₁⟩ :=
    kA_exec (P := P) c hc r0 r5 wS
  obtain ⟨c₂, t₂, e₂, ht₂, b15, f₂, m₂, rr₂, rm₂, o₂⟩ := kI0_exec (P := P) c₁ e₁.wb_right
  have q₂ : ∀ x, x ≠ 9115 → (x < 9106 ∨ 9114 < x) → c₂.nreg x = c.nreg x := fun x h1 h2 => by
    rw [f₂ x h1, f₁ x h2]
  have p₂ : ∀ x, 9106 ≤ x → x ≤ 9114 → c₂.nreg x = c₁.nreg x := fun x h1 h2 => f₂ x (by omega)
  -- `IND := 0`
  obtain ⟨c₃, t₃, e₃, ht₃, z₃, k₃, f₃, rr₃, rm₃, o₃⟩ := kZL_exec (P := P) c₂ e₂.wb_right
    (A := S + m) (m := m) (by rw [q₂ _ (by omega) (by omega), r0])
    (by rw [p₂ _ (by omega) (by omega), a8]) b15 (by rw [p₂ _ (by omega) (by omega), a6])
    (by rw [p₂ _ (by omega) (by omega), a7]) (by omega)
  obtain ⟨c₄, t₄, e₄, ht₄, b15', f₄, m₄, rr₄, rm₄, o₄⟩ := kI0_exec (P := P) c₃ e₃.wb_right
  have q₄ : ∀ x, x ≠ 9115 → x ≠ 9116 → (x < 9106 ∨ 9114 < x) → c₄.nreg x = c.nreg x :=
    fun x h1 h2 h3 => by rw [f₄ x h1, f₃ x h1 h2, q₂ x h1 h3]
  have p₄ : ∀ x, 9106 ≤ x → x ≤ 9114 → c₄.nreg x = c₁.nreg x := fun x h1 h2 => by
    rw [f₄ x (by omega), f₃ x (by omega) (by omega), p₂ x h1 h2]
  have mem₄ : ∀ a, (a < S + m ∨ S + 2 * m ≤ a) → c₄.nmem a = c.nmem a := fun a ha => by
    rw [m₄, k₃ a (by omega), m₂, m₁]
  -- loop P
  obtain ⟨c₅, t₅, e₅, ht₅, pos₅, ind₅, k₅, f₅, rr₅, rm₅, o₅⟩ := kPL_exec (P := P) c₄ e₄.wb_right
    (m := m) (VL := VL) (RV := RV) (G := G) (Z := Z) (S := S)
    (by rw [q₄ _ (by omega) (by omega) (by omega), r0])
    (by rw [q₄ _ (by omega) (by omega) (by omega), r1])
    (by rw [q₄ _ (by omega) (by omega) (by omega), r2])
    (by rw [q₄ _ (by omega) (by omega) (by omega), r3])
    (by rw [q₄ _ (by omega) (by omega) (by omega), r4])
    (by rw [q₄ _ (by omega) (by omega) (by omega), r5])
    (by rw [p₄ _ (by omega) (by omega), a6]) (by rw [p₄ _ (by omega) (by omega), a7])
    (by rw [p₄ _ (by omega) (by omega), a8]) b15'
    (fun w hw => by rw [m₄]; exact z₃ w hw)
    (fun j hj => by rw [mem₄ _ (by rcases dR with h | h <;> omega)]; exact hRV j hj)
    (fun j hj => by rw [mem₄ _ (by rcases dV with h | h <;> omega)]; exact (hVL j hj).1)
    (by rcases dV with h | h <;> [exact Or.inl h; exact Or.inr (by omega)])
    (by rcases dR with h | h <;> [exact Or.inl h; exact Or.inr (by omega)])
    (by rcases dG with h | h <;> [exact Or.inl h; exact Or.inr (by omega)])
    (by omega) wV wR wG
  have mem₅ : ∀ a, (a < S ∨ S + 2 * m ≤ a) → c₅.nmem a = c.nmem a := fun a ha => by
    rw [k₅ a ha, mem₄ a (by omega)]
  have eRV : ∀ j < m, c₄.nmem (RV + j) = c.nmem (RV + j) := fun j hj =>
    mem₄ _ (by rcases dR with h | h <;> omega)
  have eVL : ∀ j < m, c₄.nmem (VL + j) = c.nmem (VL + j) := fun j hj =>
    mem₄ _ (by rcases dV with h | h <;> omega)
  have eG : ∀ j < m, c₄.nmem (G + j) = c.nmem (G + j) := fun j hj =>
    mem₄ _ (by rcases dG with h | h <;> omega)
  have hkps : ∀ j < m, kps c₄.nmem G Z j = kps c.nmem G Z j := fun j hj => by
    simp only [kps, eG j hj]
  have q₅ : ∀ x, x ≠ 9115 → x ≠ 9116 → (x < 9106 ∨ 9119 < x) → c₅.nreg x = c.nreg x :=
    fun x h1 h2 h3 => by rw [f₅ x (by omega), q₄ x h1 h2 (by omega)]
  have p₅ : ∀ x, 9106 ≤ x → x ≤ 9114 → c₅.nreg x = c₁.nreg x := fun x h1 h2 => by
    rw [f₅ x (by omega), p₄ x h1 h2]
  -- the counting sort of the positive darts by tail label
  obtain ⟨c₆, t₆, e₆, ht₆, u0, u1, u2, u4, u5, u6, u7, u8, u9, f₆, m₆, rr₆, rm₆, o₆⟩ :=
    kOs_exec (P := P) c₅ e₅.wb_right
  have hLay : OsLay m m VL S (S + 3 * m) (S + 4 * m + 1) (S + 5 * m + 1) (S + 6 * m + 1)
      (S + 7 * m + 1) W (fun i => c.nmem (VL + i)) (fun i => c₅.nmem (S + i)) :=
    ⟨fun i hi _ => (hVL i hi).1, by omega, by rcases dV with h | h <;> omega, by omega, by omega,
      by omega, by omega, by rcases dV with h | h <;> omega, by omega, wV, by omega, by omega,
      by omega, by omega, by omega⟩
  have hIn : OsIn m m VL S (S + 3 * m) (S + 4 * m + 1) (S + 5 * m + 1) (S + 6 * m + 1)
      (S + 7 * m + 1) (fun i => c.nmem (VL + i)) (fun i => c₅.nmem (S + i)) c₆ :=
    ⟨by rw [u0, q₅ _ (by omega) (by omega) (by omega), r0],
      by rw [u1, q₅ _ (by omega) (by omega) (by omega), r0],
      by rw [u2, q₅ _ (by omega) (by omega) (by omega), r1],
      by rw [u4, q₅ _ (by omega) (by omega) (by omega), r5],
      by rw [u5, p₅ _ (by omega) (by omega), a10], by rw [u6, p₅ _ (by omega) (by omega), a11],
      by rw [u7, p₅ _ (by omega) (by omega), a12], by rw [u8, p₅ _ (by omega) (by omega), a13],
      by rw [u9, p₅ _ (by omega) (by omega), a14],
      fun i hi => by rw [m₆, mem₅ _ (by rcases dV with h | h <;> omega)],
      fun i hi => by rw [m₆]⟩
  obtain ⟨c₇, t₇, e₇, ht₇, hord, hsum, k₇, f₇, rr₇, rm₇, o₇⟩ :=
    nrOs_exec (P := P) hLay c₆ e₆.wb_right hIn
  have mem₇ : ∀ a, (a < S + 3 * m ∨ S + 8 * m + 1 ≤ a) → c₇.nmem a = c₅.nmem a := fun a ha => by
    rw [k₇ a (by omega) (by omega), m₆]
  have q₇ : ∀ x, x < 1500 ∨ (1520 < x ∧ x < 9106) ∨ 9119 < x → x ≠ 9115 → x ≠ 9116 →
      c₇.nreg x = c.nreg x := fun x h1 h2 h3 => by
    rw [f₇ x (by omega), f₆ x (by omega), q₅ x h2 h3 (by omega)]
  have p₇ : ∀ x, 9106 ≤ x → x ≤ 9114 → c₇.nreg x = c₁.nreg x := fun x h1 h2 => by
    rw [f₇ x (by omega), f₆ x (by omega), p₅ x h1 h2]
  -- the scan
  obtain ⟨c₈, t₈, e₈, ht₈, i15, i20, f₈, m₈, rr₈, rm₈, o₈⟩ := kI1_exec (P := P) c₇ e₇.wb_right
  obtain ⟨c₉, t₉, e₉, ht₉, t, g20, htm, hscan, k₉, f₉, rr₉, rm₉, o₉⟩ := kSL_exec (P := P) c₈
    e₈.wb_right (m := m) (VL := VL) (A := S + m) (Qb := S + 2 * m)
    (by rw [f₈ _ (by omega) (by omega), q₇ _ (by omega) (by omega) (by omega), r0])
    (by rw [f₈ _ (by omega) (by omega), q₇ _ (by omega) (by omega) (by omega), r1])
    (by rw [f₈ _ (by omega) (by omega), p₇ _ (by omega) (by omega), a6])
    (by rw [f₈ _ (by omega) (by omega), p₇ _ (by omega) (by omega), a7])
    (by rw [f₈ _ (by omega) (by omega), p₇ _ (by omega) (by omega), a8])
    (by rw [f₈ _ (by omega) (by omega), p₇ _ (by omega) (by omega), a9]) i15 i20
    (fun v hv => by rw [m₈, mem₇ _ (by rcases dV with h | h <;> omega),
      mem₅ _ (by rcases dV with h | h <;> omega)]; exact (hVL v hv).2.2)
    (by rcases dV with h | h <;> [exact Or.inl (by omega); exact Or.inr (by omega)])
    (Or.inl (by omega)) wV (by omega) (by omega)
  -- the memory before the main loop
  have eb : ∀ a, (a < S + 2 * m ∨ S + 3 * m ≤ a) → c₉.nmem a = c₇.nmem a := fun a ha => by
    rw [k₉ a (by omega), m₈]
  have eVb : ∀ v < m, c₉.nmem (VL + v) = c.nmem (VL + v) := fun v hv => by
    rw [eb _ (by rcases dV with h | h <;> omega), mem₇ _ (by rcases dV with h | h <;> omega),
      mem₅ _ (by rcases dV with h | h <;> omega)]
  have eRb : ∀ v < m, c₉.nmem (RV + v) = c.nmem (RV + v) := fun v hv => by
    rw [eb _ (by rcases dR with h | h <;> omega), mem₇ _ (by rcases dR with h | h <;> omega),
      mem₅ _ (by rcases dR with h | h <;> omega)]
  have ePb : ∀ i < m, c₉.nmem (S + i) = c₅.nmem (S + i) := fun i hi => by
    rw [eb _ (by omega), mem₇ _ (by omega)]
  have hnrF : ∀ y, nrF (fun i => c.nmem (VL + i)) (fun i => c₅.nmem (S + i)) m y =
      nrF (fun v => c₉.nmem (VL + v)) (fun i => c₉.nmem (S + i)) m y := fun y => by
    unfold nrF
    exact List.filter_congr fun i hi => by
      have := List.mem_range.1 hi
      beta_reduce; rw [eVb i this, ePb i this]
  have hK : KCtx c₉.nmem m S VL RV W := by
    refine ⟨fun y hy => ?_, fun j hj => by rw [eRb j hj]; exact hRV j hj, fun j hj => ?_,
      dV, dR, wS, wV, wR⟩
    · obtain ⟨o1, o2, o3⟩ := hord y hy
      rw [← hnrF]
      refine ⟨by rw [eb _ (by omega), eb _ (by omega)]; exact o1,
        by rw [eb _ (by omega)]; exact o2, fun t' ht' => ?_⟩
      have o4 := o3 t' ht'
      have hlen := ht'
      rw [eb (S + 5 * m + 1 + y) (by omega), eb _ (by omega)]; exact o4
    · obtain ⟨v1, v2, -⟩ := hVL j hj
      rw [eVb j hj, eVb _ v1]; exact ⟨v1, v2⟩
  -- the start of the main loop
  have hind : ∀ w < m, c₉.nmem (S + m + w) = kCnt c.nmem VL RV G Z m w := fun w hw => by
    rw [k₉ _ (by omega), m₈, mem₇ _ (by omega), ind₅ w hw]
    unfold kCnt
    congr 1
    exact filter_congr fun j hj => by
      have := mem_range.1 hj
      simp only [kps, khd, eG j this, eRV j this, eVL _ (hRV j this)]
  have hst : KSt m (fun v => c₉.nmem (VL + v)) (fun v => c₉.nmem (VL + v)) (fun j => c₉.nmem (VL + c₉.nmem (RV + j)))
      (fun i => c₉.nmem (S + i)) (fun k => c₉.nmem (S + 2 * m + k)) (fun w => c₉.nmem (S + m + w))
      0 t := by
    have hlist : kQ (fun k => c₉.nmem (S + 2 * m + k)) t =
        (List.range m).filter fun v => decide (c₉.nmem (VL + v) = v ∧ c₉.nmem (S + m + v) = 0) := by
      rw [hscan]
      unfold kScanL
      exact List.filter_congr fun v hv => by
        have := List.mem_range.1 hv
        beta_reduce
        rw [eVb v this, k₉ (S + m + v) (by omega), m₈, mem₇ _ (by rcases dV with h | h <;> omega),
          mem₅ _ (by rcases dV with h | h <;> omega)]
    refine kst_start (by rw [hlist]; exact List.nodup_range.filter _) (fun k hk => ?_)
      (fun w hw => ?_) (fun w hw => ?_)
    · have hm' : (fun k => c₉.nmem (S + 2 * m + k)) k ∈ kQ (fun k => c₉.nmem (S + 2 * m + k)) t :=
        mem_kQ.2 ⟨k, hk, rfl⟩
      rw [hlist] at hm'
      simp only [List.mem_filter, List.mem_range, decide_eq_true_eq] at hm'
      exact ⟨hm'.1, hm'.2.1⟩
    · rw [hind w hw.1]
      unfold kCnt kIn
      congr 1
      exact filter_congr fun j hj => by
        have := mem_range.1 hj
        beta_reduce
        rw [ePb j this, pos₅ j this, hkps j this, eRb j this, eVb _ (hRV j this)]
        simp [khd]
    · rw [hlist]
      simp only [List.mem_filter, List.mem_range, decide_eq_true_eq]
      exact ⟨fun h => h.2.2, fun h => ⟨hw.1, hw.2, h⟩⟩
  -- the main loop
  obtain ⟨c₁₀, t₁₀, e₁₀, ht₁₀, h21, f₁₀, m₁₀, rr₁₀, rm₁₀, o₁₀⟩ := kH0_exec (P := P) c₉ e₉.wb_right
  have q₉ : ∀ x, (x < 9115 ∨ 9120 < x) → x ≠ 9121 → c₁₀.nreg x = c₈.nreg x := fun x h1 h2 => by
    rw [f₁₀ x h2, f₉ x h1]
  obtain ⟨c₁₁, t₁₁, e₁₁, ht₁₁, t', g20', hst', o₁₁, f₁₁, rr₁₁, rm₁₁, oo₁₁⟩ := kML_exec (P := P)
    c₁₀ e₁₀.wb_right hK (t := t) (fun a ha => by rw [m₁₀])
    (by rw [q₉ _ (by omega) (by omega), f₈ _ (by omega) (by omega), q₇ _ (by omega) (by omega) (by omega), r1])
    (by rw [q₉ _ (by omega) (by omega), f₈ _ (by omega) (by omega), q₇ _ (by omega) (by omega) (by omega), r2])
    (by rw [q₉ _ (by omega) (by omega), f₈ _ (by omega) (by omega), p₇ _ (by omega) (by omega), a6])
    (by rw [q₉ _ (by omega) (by omega), f₈ _ (by omega) (by omega), p₇ _ (by omega) (by omega), a7])
    (by rw [q₉ _ (by omega) (by omega), f₈ _ (by omega) (by omega), p₇ _ (by omega) (by omega), a8])
    (by rw [q₉ _ (by omega) (by omega), f₈ _ (by omega) (by omega), p₇ _ (by omega) (by omega), a9])
    (by rw [q₉ _ (by omega) (by omega), f₈ _ (by omega) (by omega), p₇ _ (by omega) (by omega), a12])
    (by rw [q₉ _ (by omega) (by omega), f₈ _ (by omega) (by omega), p₇ _ (by omega) (by omega), a13])
    (by rw [q₉ _ (by omega) (by omega), f₈ _ (by omega) (by omega), p₇ _ (by omega) (by omega), a14])
    (by rw [f₁₀ _ (by omega), g20]) h21
    (hst.congr (fun k _ => by beta_reduce; rw [m₁₀]) (fun w _ => by beta_reduce; rw [m₁₀]))
  have hPOS : ∀ i < m, c₁₁.nmem (S + i) = kps c.nmem G Z i := fun i hi => by
    rw [o₁₁ _ (by omega), ePb i hi, pos₅ i hi, hkps i hi]
  refine ⟨c₁₁, t₁ + (t₂ + (t₃ + (t₄ + (t₅ + (t₆ + (t₇ + (t₈ + (t₉ + (t₁₀ + t₁₁))))))))),
    .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ (.seq e₅ (.seq e₆ (.seq e₇ (.seq e₈ (.seq e₉
      (.seq e₁₀ e₁₁))))))))), ?_, hPOS, t', ?_, fun a ha => ?_, fun x hx => ?_, ?_, ?_, ?_⟩
  · unfold kahnCost; unfold osCost at ht₇; omega
  · refine hst'.congrF (fun v hv => (eVb v hv).symm) (fun v hv => (eVb v hv).symm)
      (fun j hj => by beta_reduce; rw [eRb j hj, eVb _ (hRV j hj)])
      (fun i hi => by beta_reduce; rw [o₁₁ _ (by omega)])
  · rw [o₁₁ a (by omega), eb a (by omega), mem₇ a (by omega), mem₅ a (by omega)]
  · rw [f₁₁ x (by omega), q₉ x (by omega) (by omega), f₈ x (by omega) (by omega),
      q₇ x (by omega) (by omega) (by omega)]
  · rw [rr₁₁, rr₁₀, rr₉, rr₈, rr₇, rr₆, rr₅, rr₄, rr₃, rr₂, rr₁]
  · rw [rm₁₁, rm₁₀, rm₉, rm₈, rm₇, rm₆, rm₅, rm₄, rm₃, rm₂, rm₁]
  · rw [oo₁₁, o₁₀, o₉, o₈, o₇, o₆, o₅, o₄, o₃, o₂, o₁]

end BKMNW

end PlanarFlow
