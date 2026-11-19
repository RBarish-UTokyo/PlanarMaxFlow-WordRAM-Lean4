module

public import PlanarFlow.BKMNW.NrPushRun

/-!
# The visits of the push-back on the machine: the whole run

* `nr_outs`: the darts of the label `v` in increasing index are `outsL` of the darts in index
  order at the vertex of `v`;
* **`pushP_exec`**: `pushP` visits the labels of the order `Q[0 … nv)` and computes
  `K.foldl (pushAtL M (outsL M Ld) β Fr) g` for `K` the vertices of these labels
  (`Ld = (range m).map ed`), within `22 nv + 34 m + 6` steps.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace PlanarFlow

namespace BKMNW

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs NegSSSP CombMap

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F]

/-- **The darts of a label in index order** are those of its vertex in the list of all darts. -/
lemma nr_outs {M : CombMap D V F} {m : ℕ} {ed : ℕ → D} {rv vl : ℕ → ℕ}
    (hI : IxMap M m ed rv vl) {v : ℕ} (hv : v < m) (hvv : vl v = v) :
    outsL M ((List.range m).map ed) (M.tail (ed v)) = (nrF vl (fun _ => 1) m v).map ed := by
  unfold outsL nrF
  rw [List.filter_map]
  congr 1
  exact List.filter_congr fun i hi => by
    have := List.mem_range.1 hi
    simp only [Function.comp, ne_eq, one_ne_zero, not_false_eq_true, true_and]
    simp only [hI.vl_iff i this v hv, hvv]

variable {P : Input} {W : ℕ}

lemma nrF_congr {T T' K K' : ℕ → ℕ} {m : ℕ} (hT : ∀ i < m, T' i = T i)
    (hK : ∀ i < m, K' i = K i) (y : ℕ) : nrF T' K' m y = nrF T K m y := by
  unfold nrF
  exact List.filter_congr fun i hi => by
    have := List.mem_range.1 hi; rw [hT i this, hK i this]

lemma IxMap.congr {M : CombMap D V F} {m : ℕ} {ed : ℕ → D} {rv vl rv' vl' : ℕ → ℕ}
    (h : IxMap M m ed rv vl) (hr : ∀ i < m, rv' i = rv i) (hv : ∀ i < m, vl' i = vl i) :
    IxMap M m ed rv' vl' :=
  ⟨h.surj, h.inj, fun i hi => by rw [hr i hi]; exact h.rv i hi,
    fun i hi => by
      obtain ⟨a, b, c⟩ := h.vlt i hi
      rw [hv i hi, hv _ a]; exact ⟨a, b, c⟩,
    fun i hi j hj => by rw [hv i hi, hv j hj]; exact h.vl_iff i hi j hj⟩

lemma DRep.congr_vl {M : CombMap D V F} {mem : ℕ → ℕ} {DVb : ℕ} {Kd : ℤ} {m : ℕ} {ed : ℕ → D}
    {vl vl' : ℕ → ℕ} {g : D → ℤ} (h : DRep M mem DVb Kd m ed vl g) (hv : ∀ i < m, vl' i = vl i) :
    DRep M mem DVb Kd m ed vl' g := fun v hv' hvv => h v hv' (by rw [← hv v hv']; exact hvv)

/-- The flow after the visits of the first `t` labels of the order. -/
noncomputable def nrGt (M : CombMap D V F) (ed : ℕ → D) (m : ℕ) (β : V → ℤ) (Fr : Finset V)
    (g : D → ℤ) (Q : ℕ → ℕ) (t : ℕ) : D → ℤ :=
  ((kQ Q t).map fun v => M.tail (ed v)).foldl
    (pushAtL M (outsL M ((List.range m).map ed)) β Fr) g

lemma nrGt_succ (M : CombMap D V F) (ed : ℕ → D) (m : ℕ) (β : V → ℤ) (Fr : Finset V)
    (g : D → ℤ) (Q : ℕ → ℕ) (t : ℕ) :
    nrGt M ed m β Fr g Q (t + 1) =
      pushAtL M (outsL M ((List.range m).map ed)) β Fr (nrGt M ed m β Fr g Q t)
        (M.tail (ed (Q t))) := by
  simp [nrGt, kQ_succ, List.foldl_append]

/-- The degrees of the first `t` labels of the order. -/
def nrDg (vl Q : ℕ → ℕ) (m t : ℕ) : ℕ :=
  ((kQ Q t).map fun u => (nrF vl (fun _ => 1) m u).length).sum

set_option maxHeartbeats 4000000 in
/-- **The visits on the machine** (see the module docstring). -/
theorem pushP_exec (c : Config) (hc : WordsBounded W c) {M : CombMap D V F} {m : ℕ} {ed : ℕ → D}
    {G RV VL Zn DV BT FR Q nv OB OE OL : ℕ} {Kd : ℤ} {g : D → ℤ} {β : V → ℤ} {Fr : Finset V}
    (hI : IxMap M m ed (fun i => c.nmem (RV + i)) (fun i => c.nmem (VL + i)))
    (r1 : c.nreg 9151 = G) (r2 : c.nreg 9152 = RV) (r3 : c.nreg 9153 = VL)
    (r4 : c.nreg 9154 = Zn) (r5 : c.nreg 9155 = DV) (r6 : c.nreg 9156 = BT)
    (r7 : c.nreg 9157 = FR) (r8 : c.nreg 9158 = Q) (r9 : c.nreg 9159 = nv)
    (r60 : c.nreg 9160 = OB) (r61 : c.nreg 9161 = OE) (r62 : c.nreg 9162 = OL)
    (hO : ∀ v < m, c.nmem (OE + v) = c.nmem (OB + v) +
        (nrF (fun i => c.nmem (VL + i)) (fun _ => 1) m v).length ∧ c.nmem (OE + v) ≤ m ∧
      ∀ t (ht : t < (nrF (fun i => c.nmem (VL + i)) (fun _ => 1) m v).length),
        c.nmem (OL + (c.nmem (OB + v) + t)) = (nrF (fun i => c.nmem (VL + i)) (fun _ => 1) m v)[t])
    (hQn : (kQ (fun k => c.nmem (Q + k)) nv).Nodup)
    (hQ : ∀ k < nv, c.nmem (Q + k) < m ∧ c.nmem (VL + c.nmem (Q + k)) = c.nmem (Q + k))
    (hFR : ∀ v < m, c.nmem (VL + v) = v → (c.nmem (FR + v) = 0 ↔ M.tail (ed v) ∉ Fr))
    (hBT : ∀ v < m, c.nmem (VL + v) = v → (c.nmem (BT + v) : ℤ) = Kd + β (M.tail (ed v)))
    (hG : GRep c.nmem G Zn m ed g) (hD : DRep M c.nmem DV Kd m ed (fun i => c.nmem (VL + i)) g)
    (ha : M.IsAntisymm g) (hb : ZBnd Zn g) (hKd : (m + 1) * (Zn : ℤ) ≤ Kd)
    (wKd : Kd + (m + 1) * (Zn : ℤ) ≤ W) (wZ : 2 * Zn ≤ W)
    (d1 : NrSep G m DV m) (d2 : NrSep G m RV m) (d3 : NrSep G m VL m) (d4 : NrSep G m OL m)
    (d5 : NrSep DV m RV m) (d6 : NrSep DV m VL m) (d7 : NrSep DV m OL m)
    (d8 : NrSep G m OB m) (d9 : NrSep DV m OB m) (d10 : NrSep G m OE m) (d11 : NrSep DV m OE m)
    (d12 : NrSep G m Q nv) (d13 : NrSep DV m Q nv) (d14 : NrSep G m FR m)
    (d15 : NrSep DV m FR m) (d16 : NrSep G m BT m) (d17 : NrSep DV m BT m)
    (wG : G + m ≤ W) (wD : DV + m ≤ W) (wR : RV + m ≤ W) (wV : VL + m ≤ W) (wO : OL + m ≤ W)
    (wB : OB + m ≤ W) (wE : OE + m ≤ W) (wQ : Q + nv ≤ W) (wF : FR + m ≤ W) (wT : BT + m ≤ W)
    (wm : m + 1 ≤ W) :
    ∃ c' t, Exec P W pushP c c' t ∧ t ≤ 22 * nv + 34 * m + 7 ∧
      GRep c'.nmem G Zn m ed (nrGt M ed m β Fr g (fun k => c.nmem (Q + k)) nv) ∧
      DRep M c'.nmem DV Kd m ed (fun i => c.nmem (VL + i))
        (nrGt M ed m β Fr g (fun k => c.nmem (Q + k)) nv) ∧
      M.IsAntisymm (nrGt M ed m β Fr g (fun k => c.nmem (Q + k)) nv) ∧
      ZBnd Zn (nrGt M ed m β Fr g (fun k => c.nmem (Q + k)) nv) ∧
      (∀ a, (a < G ∨ G + m ≤ a) → (a < DV ∨ DV + m ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ x, x < 9163 ∨ 9179 < x → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hnv : nv ≤ m := kQ_len_le hQn fun k hk => (hQ k hk).1
  have hcard := hI.card_le
  have hZ0 : (0 : ℤ) ≤ Zn := by positivity
  set gt := nrGt M ed m β Fr g (fun k => c.nmem (Q + k)) with hgt
  obtain ⟨c₀, t₀, e₀, ht₀, a63, a64, a65, f₀, m₀, rr₀, rm₀, o₀⟩ := pA_exec (P := P) c hc (by omega)
  let I : Config → Prop := fun c' => WordsBounded W c' ∧
    (∀ x, x < 9163 ∨ 9179 < x → c'.nreg x = c.nreg x) ∧ c'.nreg 9163 = 1 ∧ c'.nreg 9164 = 0 ∧
    c'.nreg 9165 ≤ nv ∧ GRep c'.nmem G Zn m ed (gt (c'.nreg 9165)) ∧
    DRep M c'.nmem DV Kd m ed (fun i => c.nmem (VL + i)) (gt (c'.nreg 9165)) ∧
    M.IsAntisymm (gt (c'.nreg 9165)) ∧ ZBnd Zn (gt (c'.nreg 9165)) ∧
    (∀ a, (a < G ∨ G + m ≤ a) → (a < DV ∨ DV + m ≤ a) → c'.nmem a = c.nmem a) ∧
    c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output
  let Φ : Config → ℕ := fun c' => 22 * (nv - c'.nreg 9165) +
    34 * (m - nrDg (fun i => c.nmem (VL + i)) (fun k => c.nmem (Q + k)) m (c'.nreg 9165))
  have hgt0 : gt 0 = g := by simp [hgt, nrGt, kQ]
  have hI0 : I c₀ := ⟨e₀.wb_right, fun x hx => f₀ x (by omega), a63, a64, by omega,
    by rw [a65, hgt0, m₀]; exact hG, by rw [a65, hgt0, m₀]; exact hD, by rw [a65, hgt0]; exact ha,
    by rw [a65, hgt0]; exact hb, fun a _ _ => by rw [m₀], rr₀, rm₀, o₀⟩
  have hdeg : ∀ t, t ≤ nv → nrDg (fun i => c.nmem (VL + i)) (fun k => c.nmem (Q + k)) m t ≤ m :=
    fun t ht => nrF_sum_le _ (hQn.sublist (by simp only [kQ]; exact ((List.range_sublist).2 ht).map _))
  obtain ⟨c', t', ex, ⟨hw', f', g63, g64, g65, gG, gD, ga, gb, o', q1, q2, q3⟩, hn, ht'⟩ :=
    Exec.whileLtN_potential (P := P) (W := W) (a := 9165) (b := 9159) (body := pO) I Φ
      (fun c h => h.1) (fun c₁ ⟨hw, f₁, h63, h64, h65, gG, gD, ga, gb, o₁, q1, q2, q3⟩ hlt => by
        rw [f₁ 9159 (by omega), r9] at hlt
        set t := c₁.nreg 9165 with htdef
        obtain ⟨hvm, hvv⟩ := hQ t hlt
        set v := c.nmem (Q + t) with hv
        have eQ : c₁.nmem (Q + t) = v := o₁ _ (by rcases d12 with h | h <;> omega)
          (by rcases d13 with h | h <;> omega)
        have eFR : c₁.nmem (FR + v) = c.nmem (FR + v) := o₁ _ (by rcases d14 with h | h <;> omega)
          (by rcases d15 with h | h <;> omega)
        have eBT : c₁.nmem (BT + v) = c.nmem (BT + v) := o₁ _ (by rcases d16 with h | h <;> omega)
          (by rcases d17 with h | h <;> omega)
        obtain ⟨c₂, t₂, e₂, ht₂, b66, b65, b71, b72, b73, f₂, m₂, rr₂, rm₂, o₂⟩ := pO1_exec (P := P)
          c₁ hw (Q := Q) (FR := FR) (BT := BT) (DV := DV) (t := t)
          (by rw [f₁ _ (by omega), r8]) (by rw [f₁ _ (by omega), r7])
          (by rw [f₁ _ (by omega), r6]) (by rw [f₁ _ (by omega), r5]) h63 rfl (by omega)
          (by rw [eQ]; omega) (by rw [eQ]; omega) (by rw [eQ]; omega) (by omega)
        rw [eQ] at b66 b71 b72 b73
        rw [eFR] at b71
        rw [eBT] at b72
        have k2 : ∀ x, x < 9163 ∨ 9179 < x → c₂.nreg x = c.nreg x := fun x hx => by
          rw [f₂ x (by omega) (by omega) (by omega), f₁ x hx]
        have hdv := gD v hvm hvv
        have hbt := hBT v hvm hvv
        have hsucc := nrGt_succ M ed m β Fr g (fun k => c.nmem (Q + k)) t
        have hdg : nrDg (fun i => c.nmem (VL + i)) (fun k => c.nmem (Q + k)) m (t + 1) =
            nrDg (fun i => c.nmem (VL + i)) (fun k => c.nmem (Q + k)) m t +
              (nrF (fun i => c.nmem (VL + i)) (fun _ => 1) m v).length := by
          simp [nrDg, kQ_succ, hv]
        have hdg1 := hdeg (t + 1) (by omega)
        -- the three cases
        by_cases hfr : 0 < c.nmem (FR + v)
        · have hlt2 : c₂.nreg 9164 < c₂.nreg 9171 := by
            rw [f₂ _ (by omega) (by omega) (by omega), h64, b71]; exact hfr
          have hpush : gt (t + 1) = gt t := by
            rw [show gt (t + 1) = pushAtL M (outsL M ((List.range m).map ed)) β Fr (gt t)
              (M.tail (ed v)) from hsucc]
            unfold pushAtL
            rw [if_neg (fun h' => h'.1 ((hFR v hvm hvv).not.1 (by omega) |> fun h => by
              simpa using h))]
          refine ⟨c₂, t₂ + (0 + 1), .seq e₂ (.ifLtN_true hlt2 (.skip e₂.wb_right)),
            ⟨e₂.wb_right, k2, by rw [f₂ _ (by omega) (by omega) (by omega), h63],
              by rw [f₂ _ (by omega) (by omega) (by omega), h64], by rw [b65]; omega,
              by rw [b65, hpush, m₂]; exact gG, by rw [b65, hpush, m₂]; exact gD,
              by rw [b65, hpush]; exact ga, by rw [b65, hpush]; exact gb,
              fun a h1 h2 => by rw [m₂]; exact o₁ a h1 h2, by rw [rr₂, q1], by rw [rm₂, q2],
              by rw [o₂, q3]⟩, ?_⟩
          show 22 * (nv - c₂.nreg 9165) + 34 * (m - nrDg _ _ m (c₂.nreg 9165)) + _ + 2 ≤
            22 * (nv - t) + 34 * (m - nrDg _ _ m t)
          rw [b65, hdg]; omega
        · have hlt2 : ¬ c₂.nreg 9164 < c₂.nreg 9171 := by
            rw [f₂ _ (by omega) (by omega) (by omega), h64, b71]; exact hfr
          have hfr0 : M.tail (ed v) ∉ Fr := (hFR v hvm hvv).1 (by omega)
          by_cases hbd : c.nmem (BT + v) < c₁.nmem (DV + v)
          · have hlt3 : c₂.nreg 9172 < c₂.nreg 9173 := by rw [b72, b73]; exact hbd
            have eOB : c₂.nmem (OB + v) = c.nmem (OB + v) := by
              rw [m₂]; exact o₁ _ (by rcases d8 with h | h <;> omega)
                (by rcases d9 with h | h <;> omega)
            have eOE : c₂.nmem (OE + v) = c.nmem (OE + v) := by
              rw [m₂]; exact o₁ _ (by rcases d10 with h | h <;> omega)
                (by rcases d11 with h | h <;> omega)
            obtain ⟨c₃, t₃, e₃, ht₃, b67, b68, b69, f₃, m₃, rr₃, rm₃, o₃⟩ := pI1_exec (P := P) c₂
              e₂.wb_right (OB := OB) (OE := OE) (v := v)
              (by rw [k2 _ (by omega), r60]) (by rw [k2 _ (by omega), r61]) b66 (by omega) (by omega)
            rw [eOB] at b68
            rw [eOE] at b69
            rw [b72, b73] at b67
            have em3 : ∀ a, (a < G ∨ G + m ≤ a) → (a < DV ∨ DV + m ≤ a) → c₃.nmem a = c.nmem a :=
              fun a h1 h2 => by rw [m₃, m₂]; exact o₁ a h1 h2
            have eVLf : ∀ i < m, c₃.nmem (VL + i) = c.nmem (VL + i) := fun i hi =>
              em3 _ (by rcases d3 with h | h <;> omega) (by rcases d6 with h | h <;> omega)
            have eRVf : ∀ i < m, c₃.nmem (RV + i) = c.nmem (RV + i) := fun i hi =>
              em3 _ (by rcases d2 with h | h <;> omega) (by rcases d5 with h | h <;> omega)
            have hL : nrF (fun i => c₃.nmem (VL + i)) (fun _ => 1) m v =
                nrF (fun i => c.nmem (VL + i)) (fun _ => 1) m v :=
              nrF_congr (fun i hi => eVLf i hi) (fun _ _ => rfl) v
            obtain ⟨hOE, hOEm, hOL⟩ := hO v hvm
            set L := nrF (fun i => c.nmem (VL + i)) (fun _ => 1) m v with hLd
            set rem : ℤ := M.div (gt t) (M.tail (ed v)) - β (M.tail (ed v)) with hrem
            have hrem0 : 0 < rem := by omega
            have hk3 : ∀ x, x < 9163 ∨ 9179 < x → c₃.nreg x = c.nreg x := fun x hx => by
              rw [f₃ x (by omega), k2 x hx]
            obtain ⟨c₄, t₄, e₄, ht₄, gG', gD', g67, gr', ga', gb', o₄, f₄, rr₄, rm₄, oo₄⟩ :=
              pRL_exec (P := P) c₃ e₃.wb_right (M := M) (m := m) (ed := ed) (G := G) (RV := RV)
                (VL := VL) (Zn := Zn) (DV := DV) (OL := OL) (v := v) (lo := c.nmem (OB + v))
                (Kd := Kd) (g := gt t) (rem := rem)
                (hI.congr (fun i hi => eRVf i hi) (fun i hi => eVLf i hi))
                (by rw [hk3 _ (by omega), r1]) (by rw [hk3 _ (by omega), r2])
                (by rw [hk3 _ (by omega), r3]) (by rw [hk3 _ (by omega), r4])
                (by rw [hk3 _ (by omega), r5]) (by rw [hk3 _ (by omega), r62])
                (by rw [f₃ _ (by omega), f₂ _ (by omega) (by omega) (by omega), h63])
                (by rw [f₃ _ (by omega), f₂ _ (by omega) (by omega) (by omega), h64])
                (by rw [f₃ _ (by omega), b66])
                (by rw [b67]; have := Int.toNat_of_nonneg hrem0.le; omega) b68
                (by rw [b69, hL, hOE])
                (fun t' ht' => by
                  have ht'' : t' < L.length := hL ▸ ht'
                  rw [em3 _ (by rcases d4 with h | h <;> omega) (by rcases d7 with h | h <;> omega),
                    hOL t' ht'']
                  simp only [hL])
                (by rw [hL]; omega) hvm (by rw [eVLf v hvm]; exact hvv)
                (by intro i hi; rw [m₃, m₂]; exact gG i hi)
                (DRep.congr_vl (by intro u hu hu'; rw [m₃, m₂]; exact gD u hu hu')
                  (fun i hi => eVLf i hi))
                ga gb hrem0.le hKd wKd wZ d1 d2 d3 d4 d5 d6 d7 wG wD wR wV wO wm
            rw [hL] at gG' gD' g67 gr' ga' gb' ht₄
            have hpush : gt (t + 1) = (nrSt M ed L (gt t) rem L.length).1 := by
              rw [show gt (t + 1) = pushAtL M (outsL M ((List.range m).map ed)) β Fr (gt t)
                (M.tail (ed v)) from hsucc]
              unfold pushAtL
              rw [if_pos ⟨hfr0, by omega⟩, nr_outs hI hvm hvv]
              simp [nrSt, hLd, hrem]
            have hreg : c₄.nreg 9165 = t + 1 := by
              rw [f₄ _ (by omega) (by omega) (by omega) (by omega), f₃ _ (by omega), b65]
            refine ⟨c₄, t₂ + (t₃ + t₄ + 1 + 2), .seq e₂ (.ifLtN_false hlt2 (.ifLtN_true hlt3
              (.seq e₃ e₄))),
              ⟨e₄.wb_right, fun x hx => by
                rw [f₄ x (by omega) (by omega) (by omega) (by omega), hk3 x hx],
                by rw [f₄ _ (by omega) (by omega) (by omega) (by omega), f₃ _ (by omega),
                  f₂ _ (by omega) (by omega) (by omega), h63],
                by rw [f₄ _ (by omega) (by omega) (by omega) (by omega), f₃ _ (by omega),
                  f₂ _ (by omega) (by omega) (by omega), h64], by rw [hreg]; omega,
                by rw [hreg, hpush]; exact gG',
                by rw [hreg, hpush]; exact DRep.congr_vl gD' (fun i hi => (eVLf i hi).symm),
                by rw [hreg, hpush]; exact ga', by rw [hreg, hpush]; exact gb',
                fun a h1 h2 => by rw [o₄ a h1 h2]; exact em3 a h1 h2, by rw [rr₄, rr₃, rr₂, q1],
                by rw [rm₄, rm₃, rm₂, q2], by rw [oo₄, o₃, o₂, q3]⟩, ?_⟩
            show 22 * (nv - c₄.nreg 9165) + 34 * (m - nrDg _ _ m (c₄.nreg 9165)) + _ + 2 ≤
              22 * (nv - t) + 34 * (m - nrDg _ _ m t)
            rw [hreg, hdg]; omega
          · have hlt3 : ¬ c₂.nreg 9172 < c₂.nreg 9173 := by rw [b72, b73]; exact hbd
            have hpush : gt (t + 1) = gt t := by
              rw [show gt (t + 1) = pushAtL M (outsL M ((List.range m).map ed)) β Fr (gt t)
              (M.tail (ed v)) from hsucc]
              unfold pushAtL
              rw [if_neg (fun h' => by
                have := h'.2
                omega)]
            refine ⟨c₂, t₂ + (0 + 2 + 2), .seq e₂ (.ifLtN_false hlt2 (.ifLtN_false hlt3
              (.skip e₂.wb_right))),
              ⟨e₂.wb_right, k2, by rw [f₂ _ (by omega) (by omega) (by omega), h63],
                by rw [f₂ _ (by omega) (by omega) (by omega), h64], by rw [b65]; omega,
                by rw [b65, hpush, m₂]; exact gG, by rw [b65, hpush, m₂]; exact gD,
                by rw [b65, hpush]; exact ga, by rw [b65, hpush]; exact gb,
                fun a h1 h2 => by rw [m₂]; exact o₁ a h1 h2, by rw [rr₂, q1], by rw [rm₂, q2],
                by rw [o₂, q3]⟩, ?_⟩
            show 22 * (nv - c₂.nreg 9165) + 34 * (m - nrDg _ _ m (c₂.nreg 9165)) + _ + 2 ≤
              22 * (nv - t) + 34 * (m - nrDg _ _ m t)
            rw [b65, hdg]; omega) hI0
  rw [f' 9159 (by omega), r9] at hn
  have he : c'.nreg 9165 = nv := by omega
  rw [he] at gG gD ga gb
  refine ⟨c', t₀ + t', .seq e₀ ex, ?_, gG, gD, ga, gb, o', f', q1, q2, q3⟩
  have : Φ c₀ ≤ 22 * nv + 34 * m := by
    show 22 * (nv - c₀.nreg 9165) + 34 * (m - nrDg _ _ m (c₀.nreg 9165)) ≤ _
    omega
  omega

end BKMNW

end PlanarFlow
