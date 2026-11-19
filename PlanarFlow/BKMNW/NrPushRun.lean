module

public import PlanarFlow.BKMNW.NrPush

/-!
# The visits of the push-back on the machine: the reductions at one vertex

The darts of a map `M` are numbered `ed i` (`i < m`, `IxMap`: reverse index `rv`, vertex labels
`vl` with `vl (vl i) = vl i ≤ i`, equal labels iff equal tails). A flow `g` is held in memory as
`G[i] = Z + g (ed i)` (`GRep`), the net outflow at every label as `DV[v] = Kd + div g` (`DRep`).

* `IxMap.card_le`, `nr_div_bnd`;
* **`pRL_exec`**: the loop over the darts of the label `v` (the list `nrF VL 1 m v` of the darts
  of tail `v` in increasing order) computes the reductions `foldl redStep (g, rem)` along them.
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

/-- **The darts of a map as indices.** -/
structure IxMap (M : CombMap D V F) (m : ℕ) (ed : ℕ → D) (rv vl : ℕ → ℕ) : Prop where
  surj : ∀ x, ∃ i < m, ed i = x
  inj : ∀ i < m, ∀ j < m, ed i = ed j → i = j
  rv : ∀ i < m, rv i < m ∧ ed (rv i) = M.rev (ed i)
  vlt : ∀ i < m, vl i < m ∧ vl (vl i) = vl i ∧ vl i ≤ i
  vl_iff : ∀ i < m, ∀ j < m, M.tail (ed i) = M.tail (ed j) ↔ vl i = vl j

/-- The flow array holds `g`. -/
def GRep (mem : ℕ → ℕ) (Gb : ℕ) (Z : ℤ) (m : ℕ) (ed : ℕ → D) (g : D → ℤ) : Prop :=
  ∀ i < m, (mem (Gb + i) : ℤ) = Z + g (ed i)

/-- The net outflow array holds `div g` at every label. -/
def DRep (M : CombMap D V F) (mem : ℕ → ℕ) (DVb : ℕ) (Kd : ℤ) (m : ℕ) (ed : ℕ → D) (vl : ℕ → ℕ)
    (g : D → ℤ) : Prop :=
  ∀ v < m, vl v = v → (mem (DVb + v) : ℤ) = Kd + M.div g (M.tail (ed v))

/-- The flow is bounded by `Z`. -/
def ZBnd (Z : ℤ) (g : D → ℤ) : Prop := ∀ d, -Z ≤ g d ∧ g d ≤ Z

lemma IxMap.card_le {M : CombMap D V F} {m : ℕ} {ed : ℕ → D} {rv vl : ℕ → ℕ}
    (h : IxMap M m ed rv vl) : Fintype.card D ≤ m := by
  have : (univ : Finset D) ⊆ (range m).image ed := fun x _ => by
    obtain ⟨i, hi, rfl⟩ := h.surj x
    exact mem_image.2 ⟨i, mem_range.2 hi, rfl⟩
  have := card_le_card this
  rw [card_univ] at this
  exact this.trans (card_image_le.trans (by simp))

lemma nr_div_bnd {M : CombMap D V F} {Z : ℤ} {g : D → ℤ} (hg : ZBnd Z g) {m : ℕ}
    (hm : Fintype.card D ≤ m) (hZ : 0 ≤ Z) (x : V) :
    -(m * Z) ≤ M.div g x ∧ M.div g x ≤ m * Z := by
  unfold CombMap.div
  have hc : ((univ.filter fun d => M.tail d = x).card : ℤ) ≤ m := by
    have := card_filter_le (univ : Finset D) fun d => M.tail d = x
    rw [card_univ] at this; exact_mod_cast this.trans hm
  constructor
  · have := card_nsmul_le_sum (univ.filter fun d => M.tail d = x) g (-Z)
      (fun d _ => (hg d).1)
    simp only [nsmul_eq_mul] at this
    nlinarith
  · have := sum_le_card_nsmul (univ.filter fun d => M.tail d = x) g Z (fun d _ => (hg d).2)
    simp only [nsmul_eq_mul] at this
    nlinarith

lemma nr_dv_val (mem : ℕ → ℕ) (Gb DVb i r v w u a X Y : ℕ) (s1 : Gb + i ≠ DVb + u)
    (s2 : Gb + r ≠ DVb + u) :
    upd (upd (upd (upd mem (Gb + i) X) (Gb + r) Y) (DVb + v) (mem (DVb + v) - a)) (DVb + w)
      ((upd mem (DVb + v) (mem (DVb + v) - a)) (DVb + w) + a) (DVb + u) =
    if u = w then ((if w = v then mem (DVb + v) - a else mem (DVb + w)) + a)
    else (if u = v then mem (DVb + v) - a else mem (DVb + u)) := by
  by_cases h1 : u = w
  · subst h1
    by_cases h3 : u = v
    · subst h3; simp [upd_same]
    · rw [upd_same, if_pos rfl, if_neg h3, upd_other _ _ _ (by omega)]
  · rw [upd_other _ _ _ (by omega), if_neg h1]
    by_cases h2 : u = v
    · subst h2; rw [upd_same, if_pos rfl]
    · rw [upd_other _ _ _ (by omega), if_neg h2, upd_other _ _ _ (Ne.symm s2),
        upd_other _ _ _ (Ne.symm s1)]

/-- **One reduction in memory** (the memory written by `pRed`). -/
lemma nr_red_mem {M : CombMap D V F} {m : ℕ} {ed : ℕ → D} {rv vl : ℕ → ℕ}
    (hI : IxMap M m ed rv vl) {mem : ℕ → ℕ} {Gb DVb : ℕ} {Z Kd : ℤ} {g : D → ℤ} {rem : ℤ}
    (hG : GRep mem Gb Z m ed g) (hD : DRep M mem DVb Kd m ed vl g) (ha : M.IsAntisymm g)
    (hb : ZBnd Z g) (hZ : 0 ≤ Z) (hKd : (m + 1) * Z ≤ Kd) {i v : ℕ} (hi : i < m) (hv : vl i = v)
    (hpos : 0 < g (ed i)) (hrem : 0 < rem) (hsep : ∀ j < m, ∀ u < m, Gb + j ≠ DVb + u)
    {a : ℕ} (haa : (a : ℤ) = min rem (g (ed i))) :
    let mem' := upd (upd (upd (upd mem (Gb + i) (mem (Gb + i) - a)) (Gb + rv i)
      (mem (Gb + rv i) + a)) (DVb + v) (mem (DVb + v) - a)) (DVb + vl (rv i))
      ((upd mem (DVb + v) (mem (DVb + v) - a)) (DVb + vl (rv i)) + a)
    redStep M (g, rem) (ed i) = (setPair M g (ed i) (g (ed i) - a), rem - a) ∧
    GRep mem' Gb Z m ed (setPair M g (ed i) (g (ed i) - a)) ∧
    DRep M mem' DVb Kd m ed vl (setPair M g (ed i) (g (ed i) - a)) ∧
    M.IsAntisymm (setPair M g (ed i) (g (ed i) - a)) ∧
    ZBnd Z (setPair M g (ed i) (g (ed i) - a)) := by
  intro mem'
  set d := ed i with hd
  obtain ⟨hri, hrd⟩ := hI.rv i hi
  have hne : rv i ≠ i := fun e => M.rev_ne d (by rw [← hrd, e])
  have ha1 : 0 < (a : ℤ) := by rw [haa]; exact lt_min hrem hpos
  have ha2 : (a : ℤ) ≤ g d := by rw [haa]; exact min_le_right _ _
  have ha3 : (a : ℤ) ≤ rem := by rw [haa]; exact min_le_left _ _
  have hvm : v < m := hv ▸ (hI.vlt i hi).1
  have hvv : vl v = v := by rw [← hv]; exact (hI.vlt i hi).2.1
  obtain ⟨hwm, hww, -⟩ := hI.vlt (rv i) hri
  set w := vl (rv i) with hw
  have hcard := hI.card_le
  refine ⟨?_, fun j hj => ?_, fun u hu hu' => ?_, setPair_antisymm ha _ _, fun e => ?_⟩
  · simp only [redStep, hpos, hrem, and_self, ite_true]
    rw [show min rem (g d) = (a : ℤ) from haa.symm]
  · -- the flow array
    have s1 := hsep j hj v hvm
    have s2 := hsep j hj w hwm
    show ((mem' (Gb + j) : ℕ) : ℤ) = _
    simp only [mem']
    rw [upd_other _ _ _ s2, upd_other _ _ _ s1]
    by_cases e1 : j = rv i
    · subst e1
      rw [upd_same, hrd, setPair_rev]
      have := hG (rv i) hri
      rw [hrd, ha d] at this
      push_cast; omega
    · rw [upd_other _ _ _ (show Gb + j ≠ Gb + rv i by omega)]
      by_cases e2 : j = i
      · rw [e2, upd_same, setPair_self]
        have := hG i hi
        rw [← hd] at this
        have := hb d
        have h' : a ≤ mem (Gb + i) := by omega
        push_cast [h']; omega
      · rw [upd_other _ _ _ (show Gb + j ≠ Gb + i by omega), setPair_of_ne _ _
          (fun h' => e2 (hI.inj j hj i hi h'))
          (fun h' => e1 (hI.inj j hj (rv i) hri (by rw [hrd]; exact h')))]
        exact hG j hj
  · -- the net outflows
    have hdiv := div_setPair (M := M) ha d (g d - a) (M.tail (ed u))
    have ht : M.tail d = M.tail (ed u) ↔ v = u := by
      rw [hI.vl_iff i hi u hu, hv, hu']
    have hh : M.head d = M.tail (ed u) ↔ w = u := by
      rw [← M.tail_rev, ← hrd, hI.vl_iff (rv i) hri u hu, hu']
    have hDv := hD v hvm hvv
    have hDu := hD u hu hu'
    have hDw := hD w hwm hww
    have hbv := nr_div_bnd (M := M) hb hcard hZ (M.tail (ed v))
    have hbu := nr_div_bnd (M := M) hb hcard hZ (M.tail (ed u))
    have hbw := nr_div_bnd (M := M) hb hcard hZ (M.tail (ed w))
    have hmZ : (m : ℤ) * Z + Z ≤ Kd := by nlinarith
    have hav : a ≤ mem (DVb + v) := by
      have := hb d; omega
    have hval : mem' (DVb + u) = if u = w then
        ((if w = v then mem (DVb + v) - a else mem (DVb + w)) + a)
        else (if u = v then mem (DVb + v) - a else mem (DVb + u)) :=
      nr_dv_val mem Gb DVb i (rv i) v w u a _ _ (hsep i hi u hu) (hsep (rv i) hri u hu)
    rw [hval, hdiv]
    have hav' : ((mem (DVb + v) - a : ℕ) : ℤ) = mem (DVb + v) - a := by push_cast [hav]; ring
    by_cases e1 : u = w
    · have hh' : M.head d = M.tail (ed u) := hh.2 e1.symm
      rw [if_pos e1, if_pos hh']
      by_cases e3 : w = v
      · have ht' : M.tail d = M.tail (ed u) := ht.2 (e3.symm.trans e1.symm)
        rw [if_pos e3, if_pos ht']
        push_cast; rw [hav']
        rw [e1, e3] at hDu ⊢; omega
      · have ht' : ¬ M.tail d = M.tail (ed u) := fun h' => e3 (e1 ▸ (ht.1 h')).symm
        rw [if_neg e3, if_neg ht']
        push_cast
        rw [e1] at hDu ⊢; omega
    · have hh' : ¬ M.head d = M.tail (ed u) := fun h' => e1 (hh.1 h').symm
      rw [if_neg e1, if_neg hh']
      by_cases e2 : u = v
      · have ht' : M.tail d = M.tail (ed u) := ht.2 e2.symm
        rw [if_pos e2, if_pos ht', hav']
        rw [e2] at hDu ⊢; omega
      · have ht' : ¬ M.tail d = M.tail (ed u) := fun h' => e2 (ht.1 h').symm
        rw [if_neg e2, if_neg ht']
        omega
  · -- the bound
    have hbd := hb d
    simp only [setPair]
    split_ifs with h1 h2
    · subst h1; omega
    · subst h2; constructor <;> omega
    · exact hb e

variable {P : Input} {W : ℕ}

/-- The state after the reductions along the first `s` darts of the label `v`. -/
noncomputable def nrSt (M : CombMap D V F) (ed : ℕ → D) (L : List ℕ) (g : D → ℤ) (rem : ℤ)
    (s : ℕ) : (D → ℤ) × ℤ :=
  ((L.take s).map ed).foldl (redStep M) (g, rem)

lemma nrSt_succ (M : CombMap D V F) (ed : ℕ → D) {L : List ℕ} (g : D → ℤ) (rem : ℤ) {s : ℕ}
    (hs : s < L.length) :
    nrSt M ed L g rem (s + 1) = redStep M (nrSt M ed L g rem s) (ed L[s]) := by
  unfold nrSt
  rw [List.take_add_one, List.getElem?_eq_getElem hs, Option.toList_some, List.map_append,
    List.foldl_append]
  rfl

set_option maxHeartbeats 2000000 in
/-- **The reductions at the label `v`** (the loop of `pR`). -/
theorem pRL_exec (c : Config) (hc : WordsBounded W c) {M : CombMap D V F} {m : ℕ} {ed : ℕ → D}
    {G RV VL Zn DV OL v lo : ℕ} {Kd : ℤ} {g : D → ℤ} {rem : ℤ}
    (hI : IxMap M m ed (fun i => c.nmem (RV + i)) (fun i => c.nmem (VL + i)))
    (r1 : c.nreg 9151 = G) (r2 : c.nreg 9152 = RV) (r3 : c.nreg 9153 = VL)
    (r4 : c.nreg 9154 = Zn) (r5 : c.nreg 9155 = DV) (r62 : c.nreg 9162 = OL)
    (r63 : c.nreg 9163 = 1) (r64 : c.nreg 9164 = 0) (r66 : c.nreg 9166 = v)
    (r67 : c.nreg 9167 = rem.toNat) (r68 : c.nreg 9168 = lo)
    (r69 : c.nreg 9169 = lo + (nrF (fun i => c.nmem (VL + i)) (fun _ => 1) m v).length)
    (hOL : ∀ t (ht : t < (nrF (fun i => c.nmem (VL + i)) (fun _ => 1) m v).length),
      c.nmem (OL + (lo + t)) = (nrF (fun i => c.nmem (VL + i)) (fun _ => 1) m v)[t])
    (hlo : lo + (nrF (fun i => c.nmem (VL + i)) (fun _ => 1) m v).length ≤ m)
    (hv : v < m) (hvv : c.nmem (VL + v) = v)
    (hG : GRep c.nmem G Zn m ed g) (hD : DRep M c.nmem DV Kd m ed (fun i => c.nmem (VL + i)) g)
    (ha : M.IsAntisymm g) (hb : ZBnd Zn g) (hr : 0 ≤ rem) (hKd : (m + 1) * (Zn : ℤ) ≤ Kd)
    (wKd : Kd + (m + 1) * (Zn : ℤ) ≤ W) (wZ : 2 * Zn ≤ W)
    (d1 : NrSep G m DV m) (d2 : NrSep G m RV m) (d3 : NrSep G m VL m) (d4 : NrSep G m OL m)
    (d5 : NrSep DV m RV m) (d6 : NrSep DV m VL m) (d7 : NrSep DV m OL m)
    (wG : G + m ≤ W) (wD : DV + m ≤ W) (wR : RV + m ≤ W) (wV : VL + m ≤ W) (wO : OL + m ≤ W)
    (wm : m + 1 ≤ W) :
    ∃ c' t, Exec P W (.whileLtN 9168 9169 pR) c c' t ∧
      t ≤ 34 * (nrF (fun i => c.nmem (VL + i)) (fun _ => 1) m v).length + 2 ∧
      GRep c'.nmem G Zn m ed (nrSt M ed (nrF (fun i => c.nmem (VL + i)) (fun _ => 1) m v) g rem
        (nrF (fun i => c.nmem (VL + i)) (fun _ => 1) m v).length).1 ∧
      DRep M c'.nmem DV Kd m ed (fun i => c.nmem (VL + i))
        (nrSt M ed (nrF (fun i => c.nmem (VL + i)) (fun _ => 1) m v) g rem
          (nrF (fun i => c.nmem (VL + i)) (fun _ => 1) m v).length).1 ∧
      c'.nreg 9167 = (nrSt M ed (nrF (fun i => c.nmem (VL + i)) (fun _ => 1) m v) g rem
        (nrF (fun i => c.nmem (VL + i)) (fun _ => 1) m v).length).2.toNat ∧
      0 ≤ (nrSt M ed (nrF (fun i => c.nmem (VL + i)) (fun _ => 1) m v) g rem
        (nrF (fun i => c.nmem (VL + i)) (fun _ => 1) m v).length).2 ∧
      M.IsAntisymm (nrSt M ed (nrF (fun i => c.nmem (VL + i)) (fun _ => 1) m v) g rem
        (nrF (fun i => c.nmem (VL + i)) (fun _ => 1) m v).length).1 ∧
      ZBnd Zn (nrSt M ed (nrF (fun i => c.nmem (VL + i)) (fun _ => 1) m v) g rem
        (nrF (fun i => c.nmem (VL + i)) (fun _ => 1) m v).length).1 ∧
      (∀ a, (a < G ∨ G + m ≤ a) → (a < DV ∨ DV + m ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ x, x ≠ 9167 → x ≠ 9168 → x ≠ 9170 → (x < 9174 ∨ 9179 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨L, hL⟩ : ∃ L, L = nrF (fun i => c.nmem (VL + i)) (fun _ => 1) m v := ⟨_, rfl⟩
  rw [← hL] at r69 hOL hlo ⊢
  have hcard := hI.card_le
  have hZ0 : (0 : ℤ) ≤ Zn := by positivity
  let J : ℕ → Config → Prop := fun k c' =>
    (∀ x, x ≠ 9167 → x ≠ 9168 → x ≠ 9170 → (x < 9174 ∨ 9179 < x) → c'.nreg x = c.nreg x) ∧
    GRep c'.nmem G Zn m ed (nrSt M ed L g rem (k - lo)).1 ∧
    DRep M c'.nmem DV Kd m ed (fun i => c.nmem (VL + i)) (nrSt M ed L g rem (k - lo)).1 ∧
    c'.nreg 9167 = (nrSt M ed L g rem (k - lo)).2.toNat ∧ 0 ≤ (nrSt M ed L g rem (k - lo)).2 ∧
    M.IsAntisymm (nrSt M ed L g rem (k - lo)).1 ∧ ZBnd Zn (nrSt M ed L g rem (k - lo)).1 ∧
    (∀ a, (a < G ∨ G + m ≤ a) → (a < DV ∨ DV + m ≤ a) → c'.nmem a = c.nmem a) ∧
    c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output
  have h0 : ∀ k, k - lo = 0 → nrSt M ed L g rem (k - lo) = (g, rem) := fun k hk => by
    rw [hk]; simp [nrSt]
  obtain ⟨c', t, ex, ht, -, -, j1, j2, j3, j4, j5, j6, j7, j8, j9, j10, j11⟩ := lnRange (P := P)
    (a := 9168) (b := 9169) (body := pR) J (B := 32) c hc r68 r69 (by omega)
    ⟨fun _ _ _ _ _ => rfl, by rw [h0 lo (by omega)]; exact hG, by rw [h0 lo (by omega)]; exact hD,
      by rw [h0 lo (by omega), r67], by rw [h0 lo (by omega)]; exact hr,
      by rw [h0 lo (by omega)]; exact ha, by rw [h0 lo (by omega)]; exact hb, fun _ _ _ => rfl,
      rfl, rfl, rfl⟩
    (fun k c₁ hk1 hk2 hw h68 h69 ⟨f₁, gG, gD, g67, gr, ga, gb, o₁, q1, q2, q3⟩ => by
      set st := nrSt M ed L g rem (k - lo) with hst
      have hs : k - lo < L.length := by omega
      have hsucc : k + 1 - lo = (k - lo) + 1 := by omega
      set i := L[k - lo] with hi
      have hiL : i ∈ L := List.getElem_mem hs
      obtain ⟨him, -, hiv⟩ := nrF_mem (tl := fun i => c.nmem (VL + i)) (ps := fun _ => 1) (m := m)
        (u := v) (hL ▸ hiL)
      obtain ⟨hri, hrd⟩ := hI.rv i him
      obtain ⟨hwm, -, -⟩ := hI.vlt _ hri
      have eOL : c₁.nmem (OL + k) = i := by
        rw [o₁ _ (by rcases d4 with h | h <;> omega) (by rcases d7 with h | h <;> omega)]
        have := hOL (k - lo) hs; rw [show lo + (k - lo) = k by omega] at this; exact this
      have eRV : c₁.nmem (RV + i) = c.nmem (RV + i) :=
        o₁ _ (by rcases d2 with h | h <;> omega) (by rcases d5 with h | h <;> omega)
      have eVL : c₁.nmem (VL + c.nmem (RV + i)) = c.nmem (VL + c.nmem (RV + i)) :=
        o₁ _ (by rcases d3 with h | h <;> omega) (by rcases d6 with h | h <;> omega)
      have hne : i ≠ c.nmem (RV + i) := fun e => M.rev_ne (ed i) (by rw [← hrd, ← e])
      have hGi := gG i him
      have hGr := gG _ hri
      have hbi := gb (ed i)
      have hbr := gb (ed (c.nmem (RV + i)))
      have hDvv := gD v hv hvv
      have hbv := nr_div_bnd (M := M) gb hcard hZ0 (M.tail (ed v))
      have hDw := gD _ hwm (hI.vlt _ hri).2.1
      have hbw := nr_div_bnd (M := M) gb hcard hZ0 (M.tail (ed (c.nmem (VL + c.nmem (RV + i)))))
      have hmZ : (m : ℤ) * Zn + Zn ≤ Kd := by nlinarith
      have hmZ' : Kd + (m : ℤ) * Zn + Zn ≤ W := by nlinarith
      have hanti := ga (ed i)
      rw [← hrd] at hanti
      have hmin := Nat.min_le_right st.2.toNat (c₁.nmem (G + i) - Zn)
      obtain ⟨c₂, t₂, e₂, ht₂, g68, gif, f₂, rr₂, rm₂, o₂⟩ := pR_exec (P := P) c₁ hw
        (G := G) (RV := RV) (VL := VL) (Z := Zn) (DV := DV) (OL := OL) (v := v)
        (rem := st.2.toNat) (k := k)
        (by rw [f₁ _ (by omega) (by omega) (by omega) (by omega), r1])
        (by rw [f₁ _ (by omega) (by omega) (by omega) (by omega), r2])
        (by rw [f₁ _ (by omega) (by omega) (by omega) (by omega), r3])
        (by rw [f₁ _ (by omega) (by omega) (by omega) (by omega), r4])
        (by rw [f₁ _ (by omega) (by omega) (by omega) (by omega), r5])
        (by rw [f₁ _ (by omega) (by omega) (by omega) (by omega), r62])
        (by rw [f₁ _ (by omega) (by omega) (by omega) (by omega), r63])
        (by rw [f₁ _ (by omega) (by omega) (by omega) (by omega), r64])
        (by rw [f₁ _ (by omega) (by omega) (by omega) (by omega), r66]) g67 h68
        (by omega) (by omega)
        (by rw [eOL, eRV]; omega) (by rw [eOL]; rcases d2 with h | h <;> omega)
        (by rw [eOL, eRV]; rcases d6 with h | h <;> omega)
        (by rw [eOL, eRV]; rcases d3 with h | h <;> omega)
        (by rw [eOL, eRV]; rcases d3 with h | h <;> omega)
        (by rw [eOL]; rcases d1 with h | h <;> omega) (by rw [eOL, eRV]; rcases d1 with h | h <;> omega)
        (by rw [eOL, eRV, eVL]; rcases d1 with h | h <;> omega)
        (by rw [eOL, eRV, eVL]; rcases d1 with h | h <;> omega)
        (by rw [eOL]; omega) (by rw [eOL, eRV]; omega) (by rw [eOL]; omega)
        (by rw [eOL, eRV]; omega) (by omega) (by rw [eOL, eRV]; omega)
        (by rw [eOL, eRV, eVL]; omega)
        (by
          rw [eOL, eRV, eVL]
          by_cases e : DV + c.nmem (VL + c.nmem (RV + i)) = DV + v
          · rw [e, upd_same]; omega
          · rw [upd_other _ _ _ e]; omega)
      rw [eOL, eRV, eVL] at gif
      have hst1 : nrSt M ed L g rem (k + 1 - lo) = redStep M st (ed i) := by
        rw [hsucc, nrSt_succ M ed g rem hs]
      refine ⟨c₂, t₂, e₂, ht₂, g68, by rw [f₂ _ (by omega) (by omega) (by omega) (by omega)]; exact h69,
        fun x h1 h2 h3 h4 => by rw [f₂ x h1 h2 h3 h4, f₁ x h1 h2 h3 h4], ?_⟩
      rw [hst1]
      by_cases hcond : Zn < c₁.nmem (G + i) ∧ 0 < st.2.toNat
      · rw [if_pos hcond] at gif
        obtain ⟨g67', gm⟩ := gif
        have hpos : 0 < st.1 (ed i) := by omega
        have hrem : 0 < st.2 := by omega
        set a := min st.2.toNat (c₁.nmem (G + i) - Zn) with ha'
        have haa : (a : ℤ) = min st.2 (st.1 (ed i)) := by
          rw [ha']; push_cast
          rw [Int.toNat_of_nonneg gr, show ((c₁.nmem (G + i) - Zn : ℕ) : ℤ) = st.1 (ed i) by omega]
        obtain ⟨e1, e2, e3, e4, e5⟩ := nr_red_mem (M := M) hI (mem := c₁.nmem) gG gD ga gb hZ0 hKd
          him hiv hpos hrem (fun j hj u hu => by rcases d1 with h | h <;> omega) haa
        rw [e1]
        refine ⟨?_, ?_, by rw [g67']; omega, by dsimp only; omega, e4, e5, fun a' h1 h2 => ?_,
          by rw [rr₂, q1], by rw [rm₂, q2], by rw [o₂, q3]⟩
        · intro j hj; rw [gm]; exact e2 j hj
        · intro u hu hu'; rw [gm]; exact e3 u hu hu'
        · rw [gm, upd_other _ _ _ (by omega), upd_other _ _ _ (by omega),
            upd_other _ _ _ (by omega), upd_other _ _ _ (by omega)]
          exact o₁ a' h1 h2
      · rw [if_neg hcond] at gif
        obtain ⟨g67', gm⟩ := gif
        have hstep : redStep M st (ed i) = st := by
          have : ¬ (0 < st.1 (ed i) ∧ 0 < st.2) := fun h' => hcond ⟨by omega, by omega⟩
          simp only [redStep, this, ite_false]
        rw [hstep]
        refine ⟨fun j hj => by rw [gm]; exact gG j hj, fun u hu hu' => by rw [gm]; exact gD u hu hu',
          by rw [g67'], gr, ga, gb, fun a' h1 h2 => by rw [gm]; exact o₁ a' h1 h2,
          by rw [rr₂, q1], by rw [rm₂, q2], by rw [o₂, q3]⟩)
  rw [show lo + L.length - lo = L.length by omega] at j2 j3 j4 j5 j6 j7
  exact ⟨c', t, ex, by omega, j2, j3, j4, j5, j6, j7, j8, j1, j9, j10, j11⟩

end BKMNW

end PlanarFlow
