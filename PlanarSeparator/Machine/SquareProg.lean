module

public import PlanarSeparator.Machine.SquareMath

/-!
# The separator routine of the square on the machine

**`PlanarSeparator.Piece.squareProg`** computes the marks of the separation
`((ltRoutine R hR (ord N) mem_ord).square hΔ).sep U w` (`PlanarSeparator.SepRoutine.square`) of
a vertex set `U` given as the sorted list of its vertices (`SPre`):

* `sqP1`, `sqP2`: the flags `2` on `U` and `1` on the rest of the closed neighbourhood
  `U' = closedNbhd G U` in the flag array;
* `sqP3`: the bucket pass over the flag array: the sorted list of `U'` (the list area of the
  separator of the components), the weights of `U'` saved, the weights of `U' \ U` zeroed;
* `compSepProg` on `U'` (`PlanarSeparator.Piece.compSepProg_exec`, with `compSep_congr`);
* `sqP4`: the weights restored and the flags cleared;
* `sqP5`, `sqP6`: the mark `0` on the vertices of `U` in the closed neighbourhood of the
  separator, the old mark on the others; the flags cleared.

Main results: **`squareProg_exec`** (the marks `SDone` and the step bound
`15 N + 2411 #U' + (6 Δ + 3415) ∑_{U'} deg + 12 ∑_U w + 43 #U + 22 ∑_U deg + 5420`) and
`squareProg_cost_le` (the bound in terms of `#U` and `Δ`). The bucket pass costs `15 N`
per call (a merge sort of the closed neighbourhood would remove this term).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarSeparator

namespace Piece

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

variable {N : ℕ} {G : SimpleGraph (Fin N)} [DecidableRel G.Adj] {U : Finset (Fin N)}
  {w : Fin N → ℕ} {W : ℕ} {P : Input}

/-! ### A loop with a variable cost per round -/

theorem sqForN {ri rN M lo : ℕ} {body : Stmt} (f : ℕ → ℕ) (I : ℕ → Config → Prop)
    (hI : ∀ i c, I i c → WordsBounded W c ∧ c.nreg ri = i ∧ c.nreg rN = M)
    (hbody : ∀ i c, I i c → i < M → ∃ c' k, Exec P W body c c' k ∧ I (i + 1) c' ∧ k ≤ f i)
    (hlo : lo ≤ M) {c : Config} (hc : I lo c) :
    ∃ c' k, Exec P W (.whileLtN ri rN body) c c' k ∧ I M c' ∧
      k ≤ ∑ j ∈ Ico lo M, (f j + 2) + 2 := by
  obtain ⟨c', k, e, ⟨i, -, hiM, hi⟩, hn, hk⟩ := Exec.whileLtN_potential (P := P) (W := W)
    (a := ri) (b := rN) (body := body) (fun c => ∃ i, lo ≤ i ∧ i ≤ M ∧ I i c)
    (fun c => ∑ j ∈ Ico (c.nreg ri) M, (f j + 2))
    (fun c ⟨i, _, _, h⟩ => (hI i c h).1)
    (fun c ⟨i, hlo', _, h⟩ hlt => by
      obtain ⟨-, h1, h2⟩ := hI i c h
      rw [h1, h2] at hlt
      obtain ⟨c', k, e, h', hk⟩ := hbody i c h hlt
      refine ⟨c', k, e, ⟨i + 1, by omega, hlt, h'⟩, ?_⟩
      rw [(hI _ _ h').2.1, h1, Finset.sum_eq_sum_Ico_succ_bot hlt]
      omega)
    ⟨lo, le_rfl, hlo, hc⟩
  obtain ⟨-, h1, h2⟩ := hI i c' hi
  rw [h1, h2] at hn
  obtain rfl : i = M := by omega
  refine ⟨c', k, e, hi, ?_⟩
  rw [(hI lo c hc).2.1] at hk
  exact hk

/-! ### Facts on lists and neighbourhoods -/

theorem filter_lt_lv (C : Finset (Fin N)) {j : ℕ} (hj : j < #C) :
    (UN C).filter (· < lv C j) = (range j).image (lv C) := by
  have hl : ∀ {i}, i < #C → i < (clist (ord N) C).length := fun h => by
    rw [length_clist_ord]; exact h
  ext y
  simp only [mem_filter, mem_image, mem_range]
  constructor
  · rintro ⟨hy, hlt⟩
    obtain ⟨i, hi, rfl⟩ := (lv_mem_iff C).2 hy
    refine ⟨i, ?_, rfl⟩
    by_contra h
    rcases Nat.lt_or_ge j i with h' | h'
    · exact absurd (lv_inc C j i h' (hl hi)) (by omega)
    · obtain rfl : i = j := by omega
      omega
  · rintro ⟨i, hi, rfl⟩
    exact ⟨lv_mem_UN C (by omega), lv_inc C i j hi (hl hj)⟩

theorem card_filter_lt_lv (C : Finset (Fin N)) {j : ℕ} (hj : j < #C) :
    #((UN C).filter (· < lv C j)) = j := by
  rw [filter_lt_lv C hj, card_image_of_injOn, card_range]
  intro a ha b hb h
  exact lv_inj' C (by simp at ha; omega) (by simp at hb; omega) h

/-- The rank of a member of `C` in the sorted list. -/
theorem lv_card_filter (C : Finset (Fin N)) {x : ℕ} (hx : x ∈ UN C) :
    lv C #((UN C).filter (· < x)) = x := by
  obtain ⟨j, hj, rfl⟩ := (lv_mem_iff C).2 hx
  rw [card_filter_lt_lv C hj]

theorem card_filter_lt_succ (C : Finset (Fin N)) (x : ℕ) :
    #((UN C).filter (· < x + 1)) = #((UN C).filter (· < x)) + if x ∈ UN C then 1 else 0 := by
  have e : (UN C).filter (· < x + 1) = (UN C).filter (· < x) ∪ (UN C).filter (· = x) := by
    ext y; simp only [mem_filter, mem_union]
    constructor
    · rintro ⟨h1, h2⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 h2 with h | h
      · exact Or.inl ⟨h1, h⟩
      · exact Or.inr ⟨h1, h⟩
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact ⟨h1, by omega⟩
      · exact ⟨h1, by omega⟩
  rw [e, card_union_of_disjoint (disjoint_filter.2 fun _ _ h1 h2 => by omega)]
  congr 1
  split_ifs with h
  · rw [card_eq_one]; refine ⟨x, ?_⟩
    ext y; simp only [mem_filter, mem_singleton]
    constructor
    · exact fun h' => h'.2
    · rintro rfl; exact ⟨h, rfl⟩
  · rw [card_eq_zero, filter_eq_empty_iff]; rintro y hy rfl; exact h hy

theorem card_filter_lt_N (C : Finset (Fin N)) : #((UN C).filter (· < N)) = #C := by
  rw [filter_true_of_mem (fun x hx => lt_of_mem_UN hx), card_UN]

/-- The closed neighbourhood on the naturals. -/
theorem mem_UN_cl {y : ℕ} :
    y ∈ UN (closedNbhd G U) ↔ y ∈ UN U ∨ ∃ j < #U, adjN G (lv U j) y := by
  constructor
  · intro h
    obtain ⟨hy, hm⟩ := mem_UN.1 h
    obtain ⟨u, hu, hm⟩ := mem_biUnion.1 hm
    rcases mem_insert.1 hm with e | e
    · left; rw [← e] at hu; exact val_mem_UN.2 hu
    · right
      obtain ⟨j, hj, hju⟩ := (lv_mem_iff U).2 (val_mem_UN.2 hu)
      refine ⟨j, hj, ?_⟩
      rw [hju]
      exact ⟨u.2, hy, (G.mem_neighborFinset _ _).1 e⟩
  · rintro (h | ⟨j, hj, hx, hy, ha⟩)
    · obtain ⟨hy, hm⟩ := mem_UN.1 h
      exact mem_UN.2 ⟨hy, subset_closedNbhd U hm⟩
    · have hu : (⟨lv U j, hx⟩ : Fin N) ∈ U := by
        have := lv_mem_UN U hj
        exact val_mem_UN.1 this
      exact mem_UN.2 ⟨hy, mem_closedNbhd_of_adj hu ha⟩

theorem dart_iff_adjN {x y : ℕ} (hx : x < N) :
    (∃ g, gofs G x ≤ g ∧ g < gofs G (x + 1) ∧ tlG G (rvG G g) = y) ↔ adjN G x y := by
  constructor
  · rintro ⟨g, h1, h2, rfl⟩; exact (adjN_head hx h1 h2).2
  · exact exists_dart_adjN

/-! ### The state before the program -/

variable (G) in
/-- **The state before the separator of the square**: the layout of `CLay`/`CPre` without the
list of the vertex set, the sorted list of `U` at `1200` (`#U` in `1201`), `N` in `1204`, a zero
flag array at `1202` and a save area at `1203` (above the marks). -/
structure SPre (R : Kasteleyn.RotationSystem G) (w : Fin N → ℕ) (U : Finset (Fin N)) (Z W : ℕ)
    (c : Config) : Prop where
  wb : WordsBounded W c
  one : c.nreg 1001 = 1
  r0 : c.nreg 0 = 0
  lU : c.nreg 1100 + N ≤ c.nreg 1102
  lC : c.nreg 1102 + N ≤ c.nreg 1103
  lQ : c.nreg 1103 + N ≤ c.nreg 1104
  lW : c.nreg 1104 + N + 1 ≤ c.nreg 1105
  lS : c.nreg 1105 + N + 1 ≤ c.nreg 1010
  l0 : c.nreg 1010 + N < c.nreg 1011
  l1 : c.nreg 1011 + nD G ≤ c.nreg 1012
  l2 : c.nreg 1012 + nD G ≤ c.nreg 1013
  l3 : c.nreg 1013 + nD G ≤ c.nreg 1014
  l4 : c.nreg 1014 + N ≤ c.nreg 1015
  l5 : c.nreg 1015 + N ≤ c.nreg 1017
  l6 : c.nreg 1017 + N ≤ c.nreg 1018
  l7 : c.nreg 1018 + nD G ≤ c.nreg 1019
  lA : c.nreg 1019 + N ≤ c.nreg 1200
  lB : c.nreg 1200 + N ≤ c.nreg 1202
  lF : c.nreg 1202 + N ≤ c.nreg 1203
  lV : c.nreg 1203 + N ≤ W
  ofs : ∀ v ≤ N, c.nmem (c.nreg 1010 + v) = gofs G v
  tl : ∀ g < nD G, c.nmem (c.nreg 1011 + g) = tlG G g
  rv : ∀ g < nD G, c.nmem (c.nreg 1012 + g) = rvG G g
  wt : ∀ v < N, c.nmem (c.nreg 1014 + v) = SepProg.wI w v
  cid : ∀ x < N, c.nmem (c.nreg 1102 + x) = 0
  cw : ∀ j ≤ N, c.nmem (c.nreg 1104 + j) = 0
  sn : ∀ j ≤ N, c.nmem (c.nreg 1105 + j) = 0
  ro : ∀ g < nD G, c.nmem (c.nreg 1013 + g) = roG G R g
  lab : ∀ x < N, c.nmem (c.nreg 1017 + x) = 0
  rk : ∀ g < nD G, c.nmem (c.nreg 1018 + g) = 0
  lZ : Z ≤ c.nreg 1100
  zero : ∀ a < Z, c.nmem a = 0
  zreg : ∀ r < 1000, c.nreg r = 0
  rz : ∀ r, r < 1000 ∨ r = 1060 ∨ r = 1001 → c.rreg r = 0
  rmz : ∀ a < Z, c.rmem a = 0
  nN : c.nreg 1204 = N
  uu : c.nreg 1201 = #U
  ul : ∀ l < #U, c.nmem (c.nreg 1200 + l) = lv U l
  fz : ∀ x < N, c.nmem (c.nreg 1202 + x) = 0
  sw : 6 * ∑ v ∈ U, w v ≤ W
  big : 2 * bB #(closedNbhd G U) (mI G (closedNbhd G U)) (∑ v ∈ U, w v) ≤ Z

/-! ### The flags -/

/-- The flag `2` on `U`. -/
def sqP1Body : Stmt := block [.addN 1211 1200 1210, .loadN 1212 1211, .addN 1211 1202 1212,
  .storeN 1211 1205, .addN 1210 1210 1001]

/-- **The flags `2` on `U`** (and the constant `2` in `1205`). -/
def sqP1 : Stmt := .seq (block [.constN 1210 0, .constN 1205 2]) (.whileLtN 1210 1201 sqP1Body)

theorem sqP1_exec {d : Config} (hw : WordsBounded W d) {a0 aF : ℕ} (hW : N + 2 ≤ W)
    (h01 : d.nreg 1001 = 1) (h00 : d.nreg 1200 = a0) (h02 : d.nreg 1202 = aF)
    (h1201 : d.nreg 1201 = #U) (hU : ∀ l < #U, d.nmem (a0 + l) = lv U l)
    (l1 : a0 + N ≤ aF) (l2 : aF + N ≤ W) :
    ∃ d' k, Exec P W sqP1 d d' k ∧ WordsBounded W d' ∧ d'.nreg 1205 = 2 ∧
      (∀ x < N, d'.nmem (aF + x) = if x ∈ UN U then 2 else d.nmem (aF + x)) ∧
      (∀ a, (a < aF ∨ aF + N ≤ a) → d'.nmem a = d.nmem a) ∧
      (∀ r, r ≠ 1205 → r ≠ 1210 → r ≠ 1211 → r ≠ 1212 → d'.nreg r = d.nreg r) ∧
      k ≤ 7 * #U + 4 := by
  have hUN := card_le_N U
  let I : ℕ → Config → Prop := fun i d' => WordsBounded W d' ∧ d'.nreg 1210 = i ∧
    d'.nreg 1201 = #U ∧ d'.nreg 1205 = 2 ∧
    (∀ r, r ≠ 1205 → r ≠ 1210 → r ≠ 1211 → r ≠ 1212 → d'.nreg r = d.nreg r) ∧
    (∀ x < N, d'.nmem (aF + x) = if ∃ j < i, lv U j = x then 2 else d.nmem (aF + x)) ∧
    (∀ a, (a < aF ∨ aF + N ≤ a) → d'.nmem a = d.nmem a)
  obtain ⟨d₀, k₀, e₀, h₀, hk₀⟩ : ∃ d₀ k₀, Exec P W (block [.constN 1210 0, .constN 1205 2])
      d d₀ k₀ ∧ I 0 d₀ ∧ k₀ = 2 := by
    exec_block
    · omega
    · omega
    · refine ⟨⟨‹WordsBounded _ _›, by config_simp, by config_simp; exact h1201, by config_simp,
        fun r h1 h2 _ _ => by simp [h1, h2], fun x _ => by simp, fun _ _ => rfl⟩, rfl⟩
  obtain ⟨d₁, k₁, e₁, h₁, hk₁⟩ := Exec.forN (P := P) (W := W) (ri := 1210) (rN := 1201)
    (N := #U) (lo := 0) (B := 5) (body := sqP1Body) I (fun i d' h => ⟨h.1, h.2.1, h.2.2.1⟩)
    (fun i d' h hi => by
      obtain ⟨hw', h10, h01', h05, hq, hF, hfr⟩ := h
      have hx := lv_ltN U hi
      have r00 : d'.nreg 1200 = a0 := by
        rw [hq 1200 (by omega) (by omega) (by omega) (by omega), h00]
      have r02 : d'.nreg 1202 = aF := by
        rw [hq 1202 (by omega) (by omega) (by omega) (by omega), h02]
      have r1 : d'.nreg 1001 = 1 := by
        rw [hq 1001 (by omega) (by omega) (by omega) (by omega), h01]
      have mU : d'.nmem (a0 + i) = lv U i := by rw [hfr _ (Or.inl (by omega))]; exact hU i hi
      unfold sqP1Body
      exec_block
      · rw [r00, h10]; omega
      · config_simp; rw [r02, r00, h10, mU]; omega
      · config_simp; rw [h10]; omega
      · refine ⟨⟨‹WordsBounded _ _›, by config_simp; rw [h10, r1], by config_simp; exact h01',
          by config_simp; exact h05, fun r a b c' e => ?_, fun y hy => ?_, fun a ha => ?_⟩,
          by omega⟩
        · simp only [upd_apply, b, c', e, ite_false]; exact hq r a b c' e
        · simp only
          rw [r02, r00, h10, mU, h05]
          simp only [upd_apply]
          split_ifs with h1 h2 h2
          · rfl
          · exact absurd ⟨i, Nat.lt_succ_self _, by omega⟩ h2
          · obtain ⟨j, hj, hjx⟩ := h2
            rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
            · rw [hF y hy, iteT ⟨j, hj, hjx⟩]
            · omega
          · rw [hF y hy, iteF (fun ⟨j, hj, hjx⟩ => h2 ⟨j, by omega, hjx⟩)]
        · simp only
          rw [r02, r00, h10, mU, upd_other _ _ _ (by omega)]; exact hfr a ha)
    (Nat.zero_le _) h₀
  obtain ⟨hw₁, -, -, h05₁, hq₁, hF₁, hfr₁⟩ := h₁
  refine ⟨d₁, k₀ + k₁, .seq e₀ e₁, hw₁, h05₁, fun x hx => ?_, hfr₁, hq₁, by omega⟩
  rw [hF₁ x hx]
  by_cases h : x ∈ UN U
  · rw [iteT ((lv_mem_iff U).2 h), iteT h]
  · rw [iteF (fun h' => h ((lv_mem_iff U).1 h')), iteF h]

/-! ### The flags `1` on the neighbours -/

/-- The dart `g` (`1213`) of `u`: its head `z`; the flag of `z` set to `1` if it is `0`. -/
def sqP2Dart : Stmt :=
  .seq (block [.addN 1211 1012 1213, .loadN 1215 1211, .addN 1211 1011 1215, .loadN 1215 1211,
    .addN 1211 1202 1215, .loadN 1216 1211])
    (.seq (.ifLtN 1216 1001 (.instr (.storeN 1211 1001)) .skip) (.instr (.addN 1213 1213 1001)))

theorem sqP2Dart_exec {d : Config} (hw : WordsBounded W d) {aT aR aF g : ℕ}
    (h01 : d.nreg 1001 = 1) (h11 : d.nreg 1011 = aT) (h12 : d.nreg 1012 = aR)
    (h02 : d.nreg 1202 = aF) (h13 : d.nreg 1213 = g) (hg : g < nD G)
    (hrv : d.nmem (aR + g) = rvG G g) (htl : d.nmem (aT + rvG G g) = tlG G (rvG G g))
    (hz : tlG G (rvG G g) < N) (b1 : aR + nD G ≤ W) (b2 : aT + nD G ≤ W) (b3 : aF + N ≤ W) :
    ∃ d' k, Exec P W sqP2Dart d d' k ∧ WordsBounded W d' ∧ d'.nreg 1213 = g + 1 ∧
      (∀ r, r ≠ 1211 → r ≠ 1213 → r ≠ 1215 → r ≠ 1216 → d'.nreg r = d.nreg r) ∧
      d'.nmem = (if d.nmem (aF + tlG G (rvG G g)) = 0 then
        upd d.nmem (aF + tlG G (rvG G g)) 1 else d.nmem) ∧ k = 9 := by
  have hrl := rvG_lt (G := G) hg
  refine spec_seq ?_
  exec_block
  · rw [h12, h13]; omega
  · config_simp; rw [h11, h12, h13, hrv]; omega
  · config_simp; rw [h02, h11, h12, h13, hrv, htl]; omega
  · refine spec_seq ?_
    by_cases h0 : d.nmem (aF + tlG G (rvG G g)) = 0
    · refine spec_ifLtN_true (by config_simp; rw [h02, h11, h12, h13, hrv, htl, h0, h01]; omega) ?_
      refine spec_instr (Exec.storeN ‹_› _ _) fun hw₁ => ?_
      refine spec_instr (Exec.addN hw₁ _ _ _ (by config_simp; rw [h13]; omega)) fun hw₂ => ?_
      refine ⟨hw₂, by config_simp; rw [h13, h01], fun r a b c e => ?_, ?_, rfl⟩
      · simp only [upd_apply, a, b, c, e, ite_false]
      · config_simp; rw [iteT h0, h02, h11, h12, h13, hrv, htl, h01]
    · refine spec_ifLtN_false (by config_simp; rw [h02, h11, h12, h13, hrv, htl, h01]; omega) ?_
      refine spec_skip ‹_› ?_
      refine spec_instr (Exec.addN ‹_› _ _ _ (by config_simp; rw [h13]; omega)) fun hw₂ => ?_
      refine ⟨hw₂, by config_simp; rw [h13, h01], fun r a b c e => ?_, ?_, rfl⟩
      · simp only [upd_apply, a, b, c, e, ite_false]
      · config_simp; rw [iteF h0]

open scoped Classical in
/-- The flags after the neighbours of `U` satisfying `A` are flagged. -/
noncomputable def fv (U : Finset (Fin N)) (A : ℕ → Prop) (x : ℕ) : ℕ :=
  if x ∈ UN U then 2 else if A x then 1 else 0

open scoped Classical in
theorem fv_congr {A B : ℕ → Prop} {x : ℕ} (h : A x ↔ B x) : fv U A x = fv U B x := by
  unfold fv
  by_cases h1 : x ∈ UN U
  · rw [iteT h1, iteT h1]
  · rw [iteF h1, iteF h1]
    by_cases h2 : A x
    · rw [iteT h2, iteT (h.1 h2)]
    · rw [iteF h2, iteF (fun h' => h2 (h.2 h'))]

/-- The darts of `u` (`1212`) from `1213` below `1214`. -/
def sqP2Body : Stmt :=
  .seq (block [.addN 1211 1200 1210, .loadN 1212 1211, .addN 1211 1010 1212, .loadN 1213 1211,
    .addN 1211 1211 1001, .loadN 1214 1211])
    (.seq (.whileLtN 1213 1214 sqP2Dart) (.instr (.addN 1210 1210 1001)))

/-- **The flags `1` on the neighbours of `U`** without the flag `2`. -/
def sqP2 : Stmt := .seq (.instr (.constN 1210 0)) (.whileLtN 1210 1201 sqP2Body)

variable (G) in
/-- The address facts of the flag passes. -/
structure FLay (W : ℕ) (d : Config) (a0 aF : ℕ) : Prop where
  wb : WordsBounded W d
  one : d.nreg 1001 = 1
  h00 : d.nreg 1200 = a0
  h02 : d.nreg 1202 = aF
  l0 : d.nreg 1010 + N < d.nreg 1011
  l1 : d.nreg 1011 + nD G ≤ d.nreg 1012
  l2 : d.nreg 1012 + nD G ≤ a0
  lB : a0 + N ≤ aF
  lF : aF + N ≤ W
  ofs : ∀ v ≤ N, d.nmem (d.nreg 1010 + v) = gofs G v
  tl : ∀ g < nD G, d.nmem (d.nreg 1011 + g) = tlG G g
  rv : ∀ g < nD G, d.nmem (d.nreg 1012 + g) = rvG G g

/-- The `FLay` facts survive a step that keeps the registers below `1210` and the memory
outside the flag array. -/
theorem FLay.mono {d d' : Config} {a0 aF : ℕ} (h : FLay G W d a0 aF) (hw : WordsBounded W d')
    (hr : ∀ r, r < 1205 → d'.nreg r = d.nreg r)
    (hm : ∀ a, (a < aF ∨ aF + N ≤ a) → d'.nmem a = d.nmem a) : FLay G W d' a0 aF := by
  have := h.l0; have := h.l1; have := h.l2; have := h.lB
  have e10 := hr 1010 (by omega); have e11 := hr 1011 (by omega); have e12 := hr 1012 (by omega)
  have g := gofs_le G
  exact { wb := hw, one := by rw [hr 1001 (by omega)]; exact h.one
          h00 := by rw [hr 1200 (by omega)]; exact h.h00
          h02 := by rw [hr 1202 (by omega)]; exact h.h02
          l0 := by rw [e10, e11]; exact h.l0
          l1 := by rw [e11, e12]; exact h.l1
          l2 := by rw [e12]; exact h.l2
          lB := h.lB, lF := h.lF
          ofs := fun v hv => by rw [e10, hm _ (Or.inl (by omega))]; exact h.ofs v hv
          tl := fun g hg => by rw [e11, hm _ (Or.inl (by omega))]; exact h.tl g hg
          rv := fun g hg => by rw [e12, hm _ (Or.inl (by omega))]; exact h.rv g hg }

/-- The darts of one vertex `u < N`: the flag `1` on its neighbours without a flag. -/
theorem sqP2Darts_exec {d : Config} {a0 aF u : ℕ} (hL : FLay G W d a0 aF) (hu : u < N)
    (h13 : d.nreg 1213 = gofs G u) (h14 : d.nreg 1214 = gofs G (u + 1)) (A : ℕ → Prop)
    (hF : ∀ x < N, d.nmem (aF + x) = fv U A x) :
    ∃ d' k, Exec P W (.whileLtN 1213 1214 sqP2Dart) d d' k ∧ WordsBounded W d' ∧
      (∀ r, r ≠ 1211 → r ≠ 1213 → r ≠ 1215 → r ≠ 1216 → d'.nreg r = d.nreg r) ∧
      (∀ x < N, d'.nmem (aF + x) = fv U (fun x => A x ∨ adjN G u x) x) ∧
      (∀ a, (a < aF ∨ aF + N ≤ a) → d'.nmem a = d.nmem a) ∧
      k ≤ 11 * dg G u + 2 := by
  have hmono := gofs_mono (G := G) u (u + 1) (Nat.le_succ _) hu
  have hND := gofs_le G (u + 1)
  have := hL.l0; have := hL.l1; have := hL.l2; have := hL.lB; have := hL.lF
  let J : ℕ → Config → Prop := fun g d' => WordsBounded W d' ∧ gofs G u ≤ g ∧
    d'.nreg 1213 = g ∧ d'.nreg 1214 = gofs G (u + 1) ∧
    (∀ r, r ≠ 1211 → r ≠ 1213 → r ≠ 1215 → r ≠ 1216 → d'.nreg r = d.nreg r) ∧
    (∀ x < N, d'.nmem (aF + x) = fv U (fun x => A x ∨
      ∃ g', gofs G u ≤ g' ∧ g' < g ∧ tlG G (rvG G g') = x) x) ∧
    (∀ a, (a < aF ∨ aF + N ≤ a) → d'.nmem a = d.nmem a)
  obtain ⟨d₁, k₁, e₁, h₁, hk₁⟩ := Exec.forN (P := P) (W := W) (ri := 1213) (rN := 1214)
    (N := gofs G (u + 1)) (lo := gofs G u) (B := 9) (body := sqP2Dart) J
    (fun g d' h => ⟨h.1, h.2.2.1, h.2.2.2.1⟩)
    (fun g d' h hg => by
      obtain ⟨hw', hlo, h13', h14', hq, hF', hfr⟩ := h
      have hgD : g < nD G := lt_of_lt_of_le hg hND
      obtain ⟨hzN, -⟩ := adjN_head hu hlo hg
      have r01 : d'.nreg 1001 = 1 := by
        rw [hq 1001 (by omega) (by omega) (by omega) (by omega)]; exact hL.one
      have r11 : d'.nreg 1011 = d.nreg 1011 := hq 1011 (by omega) (by omega) (by omega) (by omega)
      have r12 : d'.nreg 1012 = d.nreg 1012 := hq 1012 (by omega) (by omega) (by omega) (by omega)
      have r02 : d'.nreg 1202 = aF := by
        rw [hq 1202 (by omega) (by omega) (by omega) (by omega)]; exact hL.h02
      have hrl := rvG_lt (G := G) hgD
      obtain ⟨d₂, k₂, e₂, hw₂, c13, q₂, m₂, hk₂⟩ := sqP2Dart_exec (P := P) hw' r01 r11 r12 r02
        h13' hgD (by rw [hfr _ (Or.inl (by omega))]; exact hL.rv g hgD)
        (by rw [hfr _ (Or.inl (by omega))]; exact hL.tl _ hrl) hzN (by omega) (by omega) hL.lF
      refine ⟨d₂, k₂, e₂, ⟨hw₂, by omega, c13, by
        rw [q₂ 1214 (by omega) (by omega) (by omega) (by omega)]; exact h14',
        fun r a b c e => by rw [q₂ r a b c e, hq r a b c e], fun x hx => ?_, fun a ha => ?_⟩,
        by omega⟩
      · set z := tlG G (rvG G g) with hz
        have key : (fun x => A x ∨ ∃ g', gofs G u ≤ g' ∧ g' < g + 1 ∧ tlG G (rvG G g') = x) =
            fun x => (A x ∨ ∃ g', gofs G u ≤ g' ∧ g' < g ∧ tlG G (rvG G g') = x) ∨ x = z := by
          funext x; apply propext; constructor
          · rintro (h | ⟨g', h1, h2, h3⟩)
            · exact Or.inl (Or.inl h)
            · rcases Nat.lt_succ_iff_lt_or_eq.1 h2 with h2 | rfl
              · exact Or.inl (Or.inr ⟨g', h1, h2, h3⟩)
              · exact Or.inr h3.symm
          · rintro ((h | ⟨g', h1, h2, h3⟩) | rfl)
            · exact Or.inl h
            · exact Or.inr ⟨g', h1, by omega, h3⟩
            · exact Or.inr ⟨g, hlo, by omega, rfl⟩
        rw [key, m₂]
        by_cases hxz : x = z
        · subst hxz
          have e := hF' _ hx
          split_ifs with h0
          · rw [upd_same]; rw [e] at h0; unfold fv at h0 ⊢; split_ifs at h0 ⊢ <;> simp_all
          · rw [e] at h0 ⊢; unfold fv at h0 ⊢; split_ifs at h0 ⊢ <;> simp_all
        · have e : d'.nmem (aF + x) = _ := hF' x hx
          split_ifs
          · rw [upd_other _ _ _ (by omega), e]; exact fv_congr (by simp [hxz])
          · rw [e]; exact fv_congr (by simp [hxz])
      · rw [m₂]; split_ifs
        · rw [upd_other _ _ _ (by omega)]; exact hfr a ha
        · exact hfr a ha)
    hmono ⟨hL.wb, le_rfl, h13, h14, fun r _ _ _ _ => rfl, fun x hx => by
      rw [hF x hx]; refine fv_congr ?_
      constructor
      · exact fun h => Or.inl h
      · rintro (h | ⟨g', h1, h2, -⟩)
        · exact h
        · omega, fun _ _ => rfl⟩
  obtain ⟨hw₁, -, -, -, hq₁, hF₁, hfr₁⟩ := h₁
  refine ⟨d₁, k₁, e₁, hw₁, hq₁, fun x hx => ?_, hfr₁, ?_⟩
  · rw [hF₁ x hx]; refine fv_congr ?_
    rw [← dart_iff_adjN hu]
  · unfold dg; omega

theorem sum_dg_lv (U : Finset (Fin N)) (a b : ℕ) :
    ∑ j ∈ Ico 0 #U, (a * dg G (lv U j) + b) = a * ∑ v ∈ U, G.degree v + b * #U := by
  rw [← range_eq_Ico, sum_add_distrib, ← mul_sum, sum_lv_eq U (dg G), sum_dg, sum_const,
    card_range, smul_eq_mul, mul_comm b]

theorem sqP2_exec {d : Config} {a0 aF : ℕ} (hL : FLay G W d a0 aF) (hW : N + 2 ≤ W)
    (h1201 : d.nreg 1201 = #U) (hU : ∀ l < #U, d.nmem (a0 + l) = lv U l)
    (hF : ∀ x < N, d.nmem (aF + x) = if x ∈ UN U then 2 else 0) :
    ∃ d' k, Exec P W sqP2 d d' k ∧ WordsBounded W d' ∧
      (∀ r, r < 1210 ∨ 1216 < r → d'.nreg r = d.nreg r) ∧
      (∀ x < N, d'.nmem (aF + x) =
        if x ∈ UN U then 2 else if x ∈ UN (closedNbhd G U) then 1 else 0) ∧
      (∀ a, (a < aF ∨ aF + N ≤ a) → d'.nmem a = d.nmem a) ∧
      k ≤ 11 * ∑ v ∈ U, G.degree v + 11 * #U + 3 := by
  have hUN := card_le_N U
  have := hL.l0; have := hL.l1; have := hL.l2; have := hL.lB; have := hL.lF
  let I : ℕ → Config → Prop := fun i d' => WordsBounded W d' ∧ d'.nreg 1210 = i ∧
    d'.nreg 1201 = #U ∧ (∀ r, r < 1210 ∨ 1216 < r → d'.nreg r = d.nreg r) ∧
    (∀ x < N, d'.nmem (aF + x) = fv U (fun x => ∃ j < i, adjN G (lv U j) x) x) ∧
    (∀ a, (a < aF ∨ aF + N ≤ a) → d'.nmem a = d.nmem a)
  have e0 := Exec.constN (P := P) hL.wb 1210 0 (Nat.zero_le _)
  obtain ⟨d₁, k₁, e₁, h₁, hk₁⟩ := sqForN (P := P) (W := W) (ri := 1210) (rN := 1201)
    (M := #U) (lo := 0) (body := sqP2Body) (fun i => 11 * dg G (lv U i) + 9) I
    (fun i d' h => ⟨h.1, h.2.1, h.2.2.1⟩)
    (fun i d' h hi => by
      obtain ⟨hw', h10, h01', hq, hF', hfr⟩ := h
      have hL' := hL.mono hw' (fun r hr => hq r (Or.inl (by omega))) hfr
      have hu := lv_ltN U hi
      have mU : d'.nmem (a0 + i) = lv U i := by rw [hfr _ (Or.inl (by omega))]; exact hU i hi
      have r10 : d'.nreg 1010 = d.nreg 1010 := hq 1010 (Or.inl (by omega))
      have mO : ∀ v ≤ N, d'.nmem (d.nreg 1010 + v) = gofs G v := fun v hv => by
        rw [← r10]; exact hL'.ofs v hv
      obtain ⟨d₂, k₂, e₂, hw₂, c12, c13, c14, q₂, m₂, hk₂⟩ : ∃ d₂ k₂, Exec P W
          (block [.addN 1211 1200 1210, .loadN 1212 1211, .addN 1211 1010 1212, .loadN 1213 1211,
          .addN 1211 1211 1001, .loadN 1214 1211]) d' d₂ k₂ ∧ WordsBounded W d₂ ∧
          d₂.nreg 1212 = lv U i ∧
          d₂.nreg 1213 = gofs G (lv U i) ∧ d₂.nreg 1214 = gofs G (lv U i + 1) ∧
          (∀ r, r ≠ 1211 → r ≠ 1212 → r ≠ 1213 → r ≠ 1214 → d₂.nreg r = d'.nreg r) ∧
          d₂.nmem = d'.nmem ∧ k₂ = 6 := by
        have hw := hw'
        exec_block
        · rw [hL'.h00, h10]; omega
        · config_simp; rw [r10, hL'.h00, h10, mU]; omega
        · config_simp; rw [r10, hL'.h00, h10, mU, hL'.one]; omega
        · refine ⟨‹_›, ?_, ?_, ?_, fun r a b c e => ?_, rfl, rfl⟩
          · config_simp; rw [hL'.h00, h10, mU]
          · config_simp; rw [r10, hL'.h00, h10, mU, mO _ hu.le]
          · config_simp; rw [r10, hL'.h00, h10, mU, hL'.one, Nat.add_assoc, mO _ hu]
          · simp only [upd_apply, a, b, c, e, ite_false]
      have hL₂ := hL'.mono hw₂ (fun r hr => q₂ r (by omega) (by omega) (by omega) (by omega))
        (fun a _ => by rw [m₂])
      obtain ⟨d₃, k₃, e₃, hw₃, q₃, hF₃, hfr₃, hk₃⟩ := sqP2Darts_exec (P := P) (U := U) hL₂ hu c13
        c14 (fun x => ∃ j < i, adjN G (lv U j) x) (fun x hx => by rw [m₂]; exact hF' x hx)
      have r10' : d₃.nreg 1210 = i := by
        rw [q₃ 1210 (by omega) (by omega) (by omega) (by omega),
          q₂ 1210 (by omega) (by omega) (by omega) (by omega), h10]
      have r01' : d₃.nreg 1001 = 1 := by
        rw [q₃ 1001 (by omega) (by omega) (by omega) (by omega),
          q₂ 1001 (by omega) (by omega) (by omega) (by omega)]; exact hL'.one
      have e4 := Exec.addN (P := P) hw₃ 1210 1210 1001 (by rw [r10', r01']; omega)
      refine ⟨_, _, .seq e₂ (.seq e₃ e4), ⟨e4.wb_right, ?_, ?_, fun r hr => ?_, fun x hx => ?_,
        fun a ha => ?_⟩, by omega⟩
      · config_simp; rw [r10', r01']
      · config_simp
        rw [q₃ 1201 (by omega) (by omega) (by omega) (by omega),
          q₂ 1201 (by omega) (by omega) (by omega) (by omega), h01']
      · config_simp
        rw [upd_other _ _ _ (by omega), q₃ r (by omega) (by omega) (by omega) (by omega),
          q₂ r (by omega) (by omega) (by omega) (by omega), hq r hr]
      · simp only
        rw [hF₃ x hx]; refine fv_congr ?_
        constructor
        · rintro (⟨j, hj, h⟩ | h)
          · exact ⟨j, by omega, h⟩
          · exact ⟨i, by omega, h⟩
        · rintro ⟨j, hj, h⟩
          rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
          · exact Or.inl ⟨j, hj, h⟩
          · exact Or.inr h
      · simp only; rw [hfr₃ a ha, m₂, hfr a ha])
    (Nat.zero_le _) ⟨e0.wb_right, by config_simp, by config_simp; exact h1201,
      fun r hr => by config_simp; rw [upd_other _ _ _ (by omega)],
      fun x hx => by
        simp only; rw [hF x hx]; unfold fv
        simp only [not_lt_zero, false_and, exists_false, ite_false],
      fun _ _ => rfl⟩
  obtain ⟨hw₁, -, -, hq₁, hF₁, hfr₁⟩ := h₁
  refine ⟨d₁, _, .seq e0 e₁, hw₁, fun r hr => ?_, fun x hx => ?_, hfr₁, ?_⟩
  · rw [hq₁ r hr]
  · rw [hF₁ x hx]; unfold fv; beta_reduce
    by_cases h : x ∈ UN U
    · rw [iteT h, iteT h]
    · rw [iteF h, iteF h]
      split_ifs with h1 h2 h2
      · rfl
      · exact absurd (mem_UN_cl.2 (Or.inr h1)) h2
      · exact absurd ((mem_UN_cl.1 h2).resolve_left h) h1
      · rfl
  · simp only [Nat.add_assoc] at hk₁; rw [sum_dg_lv] at hk₁; omega

/-! ### The bucket pass -/

/-- The vertex `x` (`1210`): if flagged, appended to the list (`1101` its length), its weight
saved, and zeroed if the flag is `1`. -/
def sqP3Body : Stmt :=
  .seq (block [.addN 1211 1202 1210, .loadN 1216 1211])
    (.seq (.ifLtN 0 1216
      (.seq (block [.addN 1211 1100 1101, .storeN 1211 1210, .addN 1211 1014 1210,
        .loadN 1215 1211, .addN 1213 1203 1101, .storeN 1213 1215, .addN 1101 1101 1001])
        (.ifLtN 1216 1205 (.instr (.storeN 1211 0)) .skip)) .skip)
      (.instr (.addN 1210 1210 1001)))

/-- **The bucket pass.** -/
def sqP3 : Stmt := .seq (block [.constN 1101 0, .constN 1210 0]) (.whileLtN 1210 1204 sqP3Body)

theorem wt_step {S T : Finset ℕ} {m : ℕ → ℕ} {aT x : ℕ} (wI : ℕ → ℕ)
    (hT : ∀ y < N, m (aT + y) = if y < x ∧ y ∈ S ∧ y ∉ T then 0 else wI y) {y : ℕ} (hy : y < N) :
    (if y < x + 1 ∧ y ∈ S ∧ y ∉ T then 0 else wI y) =
      if y = x then (if x ∈ S ∧ x ∉ T then 0 else wI x) else m (aT + y) := by
  by_cases hyx : y = x
  · subst hyx; rw [iteT rfl]
    by_cases h : y ∈ S ∧ y ∉ T
    · rw [iteT ⟨by omega, h⟩, iteT h]
    · rw [iteF (fun h' => h h'.2), iteF h]
  · rw [iteF hyx, hT y hy]
    by_cases h : y < x ∧ y ∈ S ∧ y ∉ T
    · rw [iteT ⟨by omega, h.2⟩, iteT h]
    · rw [iteF (fun h' => h ⟨by omega, h'.2⟩), iteF h]

/-- The memory step of the bucket pass. -/
theorem p3_mem {U U' : Finset (Fin N)} {aL aV aT : ℕ} (hLT : aL + N ≤ aT) (hTV : aT + N ≤ aV)
    {x : ℕ} (hx : x < N) (wI : ℕ → ℕ) {m M : ℕ → ℕ}
    (hL : ∀ l < #((UN U').filter (· < x)), m (aL + l) = lv U' l)
    (hV : ∀ l < #((UN U').filter (· < x)), m (aV + l) = wI (lv U' l))
    (hT : ∀ y < N, m (aT + y) = if y < x ∧ y ∈ UN U' ∧ y ∉ UN U then 0 else wI y)
    (hM : M = if x ∈ UN U' then
      (if x ∈ UN U then upd (upd m (aL + #((UN U').filter (· < x))) x)
          (aV + #((UN U').filter (· < x))) (m (aT + x))
        else upd (upd (upd m (aL + #((UN U').filter (· < x))) x)
          (aV + #((UN U').filter (· < x))) (m (aT + x))) (aT + x) 0) else m) :
    (∀ l < #((UN U').filter (· < x + 1)), M (aL + l) = lv U' l) ∧
    (∀ l < #((UN U').filter (· < x + 1)), M (aV + l) = wI (lv U' l)) ∧
    (∀ y < N, M (aT + y) = if y < x + 1 ∧ y ∈ UN U' ∧ y ∉ UN U then 0 else wI y) ∧
    (∀ a, (a < aL ∨ aL + N ≤ a) → (a < aV ∨ aV + N ≤ a) → (a < aT ∨ aT + N ≤ a) →
      M a = m a) := by
  have hk := card_filter_lt_succ U' x
  have hkN : #((UN U').filter (· < x + 1)) ≤ N := by
    have := card_le_N U'; rw [← card_UN] at this
    exact (card_le_card (filter_subset _ _)).trans this
  have hlv := lv_card_filter U' (x := x)
  set k := #((UN U').filter (· < x))
  subst hM
  have hW := fun y (hy : y < N) => wt_step (S := UN U') (T := UN U) wI hT hy
  by_cases h1 : x ∈ UN U'
  · have hk' : #((UN U').filter (· < x + 1)) = k + 1 := by rw [hk, iteT h1]
    rw [hk', iteT h1]
    have hmT : m (aT + x) = wI x := by rw [hT x hx, iteF (by omega)]
    have hLs : ∀ l < k + 1, upd m (aL + k) x (aL + l) = lv U' l := fun l hl => by
      by_cases e : l = k
      · subst e; rw [upd_same]; exact (hlv h1).symm
      · rw [upd_other _ _ _ (by omega)]; exact hL l (by omega)
    have hVs : ∀ l < k + 1, upd (upd m (aL + k) x) (aV + k) (m (aT + x)) (aV + l) =
        wI (lv U' l) := fun l hl => by
      by_cases e : l = k
      · subst e; rw [upd_same, hmT, hlv h1]
      · rw [upd_other _ _ _ (by omega), upd_other _ _ _ (by omega)]; exact hV l (by omega)
    by_cases h2 : x ∈ UN U
    · rw [iteT h2]
      refine ⟨fun l hl => ?_, hVs, fun y hy => ?_, fun a h3 h4 h5 => ?_⟩
      · rw [upd_other _ _ _ (by omega)]; exact hLs l hl
      · rw [hW y hy, upd_other _ _ _ (by omega), upd_other _ _ _ (by omega)]
        by_cases e : y = x
        · subst e; rw [iteT rfl, iteF (fun h => h.2 h2), hmT]
        · rw [iteF e]
      · rw [upd_other _ _ _ (by omega), upd_other _ _ _ (by omega)]
    · rw [iteF h2]
      refine ⟨fun l hl => ?_, fun l hl => ?_, fun y hy => ?_, fun a h3 h4 h5 => ?_⟩
      · rw [upd_other _ _ _ (by omega), upd_other _ _ _ (by omega)]; exact hLs l hl
      · rw [upd_other _ _ _ (by omega)]; exact hVs l hl
      · rw [hW y hy]
        by_cases e : y = x
        · subst e; rw [iteT rfl, iteT ⟨h1, h2⟩, upd_same]
        · rw [iteF e, upd_other _ _ _ (by omega), upd_other _ _ _ (by omega),
            upd_other _ _ _ (by omega)]
      · rw [upd_other _ _ _ (by omega), upd_other _ _ _ (by omega), upd_other _ _ _ (by omega)]
  · have hk' : #((UN U').filter (· < x + 1)) = k := by rw [hk, iteF h1, Nat.add_zero]
    rw [hk', iteF h1]
    refine ⟨fun l hl => hL l (by omega), fun l hl => hV l (by omega), fun y hy => ?_,
      fun _ _ _ _ => rfl⟩
    rw [hW y hy]
    by_cases e : y = x
    · subst e; rw [iteT rfl, iteF (fun h => h1 h.1), hT y hy, iteF (by omega)]
    · rw [iteF e]

theorem sqP3_exec {R : Kasteleyn.RotationSystem G} {Z : ℕ} {c d : Config}
    (hs : SPre G R w U Z W c) (hw : WordsBounded W d)
    (hr : ∀ r, r < 1205 → d.nreg r = c.nreg r) (h05 : d.nreg 1205 = 2)
    (hF : ∀ x < N, d.nmem (c.nreg 1202 + x) =
      if x ∈ UN U then 2 else if x ∈ UN (closedNbhd G U) then 1 else 0)
    (hm : ∀ a, (a < c.nreg 1202 ∨ c.nreg 1202 + N ≤ a) → d.nmem a = c.nmem a) :
    ∃ d' k, Exec P W sqP3 d d' k ∧ WordsBounded W d' ∧ d'.nreg 1101 = #(closedNbhd G U) ∧
      (∀ r, r ≠ 1101 → r ≠ 1210 → r ≠ 1211 → r ≠ 1213 → r ≠ 1215 → r ≠ 1216 →
        d'.nreg r = d.nreg r) ∧
      (∀ l < #(closedNbhd G U), d'.nmem (c.nreg 1100 + l) = lv (closedNbhd G U) l) ∧
      (∀ l < #(closedNbhd G U),
        d'.nmem (c.nreg 1203 + l) = SepProg.wI w (lv (closedNbhd G U) l)) ∧
      (∀ y < N, d'.nmem (c.nreg 1014 + y) =
        if y ∈ UN (closedNbhd G U) ∧ y ∉ UN U then 0 else SepProg.wI w y) ∧
      (∀ a, (a < c.nreg 1100 ∨ c.nreg 1100 + N ≤ a) → (a < c.nreg 1203 ∨ c.nreg 1203 + N ≤ a) →
        (a < c.nreg 1014 ∨ c.nreg 1014 + N ≤ a) → d'.nmem a = d.nmem a) ∧
      k ≤ 15 * N + 4 := by
  set U' := closedNbhd G U
  have := hs.lU; have := hs.lC; have := hs.lQ; have := hs.lW; have := hs.lS; have := hs.l0
  have := hs.l1; have := hs.l2; have := hs.l3; have := hs.l4; have := hs.l5; have := hs.l6
  have := hs.l7; have := hs.lA; have := hs.lB; have := hs.lF; have := hs.lV
  have hU'N := card_le_N U'
  set aL := c.nreg 1100 with haL
  set aF := c.nreg 1202 with haF
  set aV := c.nreg 1203 with haV
  set aT := c.nreg 1014 with haT
  have hLT : aL + N ≤ aT := by omega
  have hTV : aT + N ≤ aV := by omega
  have kf_le : ∀ x, #((UN U').filter (· < x)) ≤ N := fun x => by
    have := card_le_N U'; rw [← card_UN] at this
    exact (card_le_card (filter_subset _ _)).trans this
  let I : ℕ → Config → Prop := fun x d' => WordsBounded W d' ∧ d'.nreg 1210 = x ∧
    d'.nreg 1204 = N ∧ d'.nreg 1101 = #((UN U').filter (· < x)) ∧
    (∀ r, r ≠ 1101 → r ≠ 1210 → r ≠ 1211 → r ≠ 1213 → r ≠ 1215 → r ≠ 1216 →
      d'.nreg r = d.nreg r) ∧
    (∀ l < #((UN U').filter (· < x)), d'.nmem (aL + l) = lv U' l) ∧
    (∀ l < #((UN U').filter (· < x)), d'.nmem (aV + l) = SepProg.wI w (lv U' l)) ∧
    (∀ y < N, d'.nmem (aT + y) = if y < x ∧ y ∈ UN U' ∧ y ∉ UN U then 0 else SepProg.wI w y) ∧
    (∀ a, (a < aL ∨ aL + N ≤ a) → (a < aV ∨ aV + N ≤ a) → (a < aT ∨ aT + N ≤ a) →
      d'.nmem a = d.nmem a)
  have kf0 : #((UN U').filter (· < 0)) = 0 := by simp
  have r04 : d.nreg 1204 = N := by rw [hr 1204 (by omega)]; exact hs.nN
  obtain ⟨d₀, k₀, e₀, h₀, hk₀⟩ : ∃ d₀ k₀, Exec P W (block [.constN 1101 0, .constN 1210 0])
      d d₀ k₀ ∧ I 0 d₀ ∧ k₀ = 2 := by
    exec_block
    · omega
    · omega
    · refine ⟨⟨‹WordsBounded _ _›, by config_simp, by config_simp; exact r04,
        by config_simp; exact kf0.symm, fun r h1 h2 _ _ _ _ => by simp [h1, h2],
        fun l hl => by rw [kf0] at hl; omega, fun l hl => by rw [kf0] at hl; omega,
        fun y hy => ?_, fun _ _ _ _ => rfl⟩, rfl⟩
      simp only
      rw [hm _ (Or.inl (by omega)), hs.wt y hy]; simp
  obtain ⟨d₁, k₁, e₁, h₁, hk₁⟩ := Exec.forN (P := P) (W := W) (ri := 1210) (rN := 1204)
    (N := N) (lo := 0) (B := 13) (body := sqP3Body) I (fun i d' h => ⟨h.1, h.2.1, h.2.2.1⟩)
    (fun x d' h hx => by
      obtain ⟨hw', h10, h04, h01k, hq, hL', hV', hT', hfr⟩ := h
      have g : ∀ r, r < 1205 → r ≠ 1101 → d'.nreg r = c.nreg r := fun r h1 h2 => by
        rw [hq r h2 (by omega) (by omega) (by omega) (by omega) (by omega)]; exact hr r h1
      have g05 : d'.nreg 1205 = 2 := by
        rw [hq 1205 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]; exact h05
      have r0 : d'.nreg 0 = 0 := by rw [g 0 (by omega) (by omega)]; exact hs.r0
      have r1 : d'.nreg 1001 = 1 := by rw [g 1001 (by omega) (by omega)]; exact hs.one
      have r00 : d'.nreg 1100 = aL := g 1100 (by omega) (by omega)
      have r02 : d'.nreg 1202 = aF := g 1202 (by omega) (by omega)
      have r03 : d'.nreg 1203 = aV := g 1203 (by omega) (by omega)
      have r14 : d'.nreg 1014 = aT := g 1014 (by omega) (by omega)
      have hFx : d'.nmem (aF + x) =
          if x ∈ UN U then 2 else if x ∈ UN U' then 1 else 0 := by
        rw [hfr _ (Or.inr (by omega)) (Or.inl (by omega)) (Or.inr (by omega))]; exact hF x hx
      have hk := card_filter_lt_succ U' x
      have hkN := kf_le x
      set k := #((UN U').filter (· < x))
      have fin : ∀ d₂ : Config, WordsBounded W d₂ → d₂.nreg 1210 = x + 1 → d₂.nreg 1204 = N →
          d₂.nreg 1101 = #((UN U').filter (· < x + 1)) →
          (∀ r, r ≠ 1101 → r ≠ 1210 → r ≠ 1211 → r ≠ 1213 → r ≠ 1215 → r ≠ 1216 →
            d₂.nreg r = d'.nreg r) →
          d₂.nmem = (if x ∈ UN U' then
            (if x ∈ UN U then upd (upd d'.nmem (aL + k) x) (aV + k) (d'.nmem (aT + x))
              else upd (upd (upd d'.nmem (aL + k) x) (aV + k) (d'.nmem (aT + x))) (aT + x) 0)
            else d'.nmem) → I (x + 1) d₂ := by
        intro d₂ hw₂ c10 c04 c01 cq cm
        obtain ⟨m1, m2, m3, m4⟩ := p3_mem (U := U) (U' := U') hLT hTV hx (SepProg.wI w) hL' hV'
          hT' cm
        exact ⟨hw₂, c10, c04, c01, fun r a b c e f g' => by rw [cq r a b c e f g', hq r a b c e f g'],
          m1, m2, m3, fun a h3 h4 h5 => by rw [m4 a h3 h4 h5, hfr a h3 h4 h5]⟩
      refine spec_seq ?_
      exec_block
      · rw [r02, h10]; omega
      · refine spec_seq ?_
        by_cases h1 : x ∈ UN U'
        · refine spec_ifLtN_true (by
            config_simp; rw [r0, r02, h10, hFx]; by_cases h2 : x ∈ UN U <;> simp [h1, h2]) ?_
          refine spec_seq ?_
          exec_block
          · config_simp; rw [r00, h01k]; omega
          · config_simp; rw [r14, h10]; omega
          · config_simp; rw [r03, h01k]; omega
          · config_simp; rw [h01k, r1]; omega
          · by_cases h2 : x ∈ UN U
            · refine spec_ifLtN_false (by
                config_simp; rw [g05, r02, h10, hFx, iteT h2]; omega) ?_
              refine spec_skip ‹_› ?_
              refine spec_instr (Exec.addN ‹_› _ _ _ (by config_simp; rw [h10, r1]; omega))
                fun hw₂ => ?_
              refine ⟨fin _ hw₂ (by config_simp; rw [h10, r1]) (by config_simp; exact h04)
                (by config_simp; rw [h01k, r1, hk, iteT h1])
                (fun r a b c e f g' => by simp only [upd_apply, a, b, c, e, f, g',
                  ite_false]) (by config_simp; rw [r00, h01k, h10, r03, r14,
                  upd_other _ _ _ (by omega), iteT h1, iteT h2]), by omega⟩
            · refine spec_ifLtN_true (by
                config_simp; rw [g05, r02, h10, hFx, iteF h2, iteT h1]; omega) ?_
              refine spec_instr (Exec.storeN ‹_› _ _) fun hw₁ => ?_
              refine spec_instr (Exec.addN hw₁ _ _ _ (by config_simp; rw [h10, r1]; omega))
                fun hw₂ => ?_
              refine ⟨fin _ hw₂ (by config_simp; rw [h10, r1]) (by config_simp; exact h04)
                (by config_simp; rw [h01k, r1, hk, iteT h1])
                (fun r a b c e f g' => by simp only [upd_apply, a, b, c, e, f, g',
                  ite_false]) (by config_simp; rw [r00, h01k, h10, r03, r14, r0,
                  upd_other _ _ _ (by omega), iteT h1, iteF h2]), by omega⟩
        · refine spec_ifLtN_false (by
            config_simp; rw [r0, r02, h10, hFx, iteF (fun h2 => h1 (mem_UN_cl.2 (Or.inl h2))),
              iteF h1]; omega) ?_
          refine spec_skip ‹_› ?_
          refine spec_instr (Exec.addN ‹_› _ _ _ (by config_simp; rw [h10, r1]; omega))
            fun hw₂ => ?_
          refine ⟨fin _ hw₂ (by config_simp; rw [h10, r1]) (by config_simp; exact h04)
            (by config_simp; rw [h01k, hk, iteF h1, Nat.add_zero])
            (fun r a b c e f g' => by simp only [upd_apply, b, c, g',
              ite_false]) (by config_simp; rw [iteF h1]), by omega⟩)
    (Nat.zero_le _) h₀
  obtain ⟨hw₁, -, -, h01₁, hq₁, hL₁, hV₁, hT₁, hfr₁⟩ := h₁
  rw [card_filter_lt_N] at h01₁ hL₁ hV₁
  refine ⟨d₁, k₀ + k₁, .seq e₀ e₁, hw₁, h01₁, hq₁, hL₁, hV₁, fun y hy => ?_, hfr₁, by omega⟩
  rw [hT₁ y hy]
  by_cases h : y ∈ UN (closedNbhd G U) ∧ y ∉ UN U
  · rw [iteT ⟨hy, h⟩, iteT h]
  · rw [iteF (fun h' => h h'.2), iteF h]

/-! ### Restoring the weights, clearing the flags -/

/-- The weight of `L[i]` restored from the save area, its flag cleared. -/
def sqP4Body : Stmt := block [.addN 1211 1100 1210, .loadN 1212 1211, .addN 1213 1203 1210,
  .loadN 1215 1213, .addN 1211 1014 1212, .storeN 1211 1215, .addN 1211 1202 1212,
  .storeN 1211 0, .addN 1210 1210 1001]

/-- **The weights restored and the flags cleared** along the list of `U'`. -/
def sqP4 : Stmt := .seq (.instr (.constN 1210 0)) (.whileLtN 1210 1101 sqP4Body)

theorem sqP4_exec {C : Finset (Fin N)} (f : ℕ → ℕ) {d : Config} (hw : WordsBounded W d)
    {aL aV aT aF : ℕ} (h01 : d.nreg 1001 = 1) (h0 : d.nreg 0 = 0) (h00 : d.nreg 1100 = aL)
    (h03 : d.nreg 1203 = aV) (h14 : d.nreg 1014 = aT) (h02 : d.nreg 1202 = aF)
    (h1101 : d.nreg 1101 = #C) (hL : ∀ l < #C, d.nmem (aL + l) = lv C l)
    (hV : ∀ l < #C, d.nmem (aV + l) = f (lv C l))
    (l1 : aL + N ≤ aT) (l2 : aT + N ≤ aF) (l3 : aF + N ≤ aV) (l4 : aV + N ≤ W) :
    ∃ d' k, Exec P W sqP4 d d' k ∧ WordsBounded W d' ∧
      (∀ y < N, d'.nmem (aT + y) = if y ∈ UN C then f y else d.nmem (aT + y)) ∧
      (∀ y < N, d'.nmem (aF + y) = if y ∈ UN C then 0 else d.nmem (aF + y)) ∧
      (∀ a, (a < aT ∨ aT + N ≤ a) → (a < aF ∨ aF + N ≤ a) → d'.nmem a = d.nmem a) ∧
      (∀ r, r ≠ 1210 → r ≠ 1211 → r ≠ 1212 → r ≠ 1213 → r ≠ 1215 → d'.nreg r = d.nreg r) ∧
      k ≤ 11 * #C + 3 := by
  have hCN := card_le_N C
  let I : ℕ → Config → Prop := fun i d' => WordsBounded W d' ∧ d'.nreg 1210 = i ∧
    d'.nreg 1101 = #C ∧
    (∀ r, r ≠ 1210 → r ≠ 1211 → r ≠ 1212 → r ≠ 1213 → r ≠ 1215 → d'.nreg r = d.nreg r) ∧
    (∀ y < N, d'.nmem (aT + y) = if ∃ j < i, lv C j = y then f y else d.nmem (aT + y)) ∧
    (∀ y < N, d'.nmem (aF + y) = if ∃ j < i, lv C j = y then 0 else d.nmem (aF + y)) ∧
    (∀ a, (a < aT ∨ aT + N ≤ a) → (a < aF ∨ aF + N ≤ a) → d'.nmem a = d.nmem a)
  have e0 := Exec.constN (P := P) hw 1210 0 (Nat.zero_le _)
  obtain ⟨d₁, k₁, e₁, h₁, hk₁⟩ := Exec.forN (P := P) (W := W) (ri := 1210) (rN := 1101)
    (N := #C) (lo := 0) (B := 9) (body := sqP4Body) I (fun i d' h => ⟨h.1, h.2.1, h.2.2.1⟩)
    (fun i d' h hi => by
      obtain ⟨hw', h10, h01', hq, hT, hF, hfr⟩ := h
      have hx := lv_ltN C hi
      have r00 : d'.nreg 1100 = aL := by
        rw [hq 1100 (by omega) (by omega) (by omega) (by omega) (by omega), h00]
      have r02 : d'.nreg 1202 = aF := by
        rw [hq 1202 (by omega) (by omega) (by omega) (by omega) (by omega), h02]
      have r03 : d'.nreg 1203 = aV := by
        rw [hq 1203 (by omega) (by omega) (by omega) (by omega) (by omega), h03]
      have r14 : d'.nreg 1014 = aT := by
        rw [hq 1014 (by omega) (by omega) (by omega) (by omega) (by omega), h14]
      have r1 : d'.nreg 1001 = 1 := by
        rw [hq 1001 (by omega) (by omega) (by omega) (by omega) (by omega), h01]
      have r0 : d'.nreg 0 = 0 := by
        rw [hq 0 (by omega) (by omega) (by omega) (by omega) (by omega), h0]
      have mL : d'.nmem (aL + i) = lv C i := by
        rw [hfr _ (Or.inl (by omega)) (Or.inl (by omega))]; exact hL i hi
      have mV : d'.nmem (aV + i) = f (lv C i) := by
        rw [hfr _ (Or.inr (by omega)) (Or.inr (by omega))]; exact hV i hi
      have hnot : ∀ y, (∃ j < i + 1, lv C j = y) ↔ (∃ j < i, lv C j = y) ∨ y = lv C i :=
        fun y => ⟨fun ⟨j, hj, e⟩ => (Nat.lt_succ_iff_lt_or_eq.1 hj).elim (fun h => Or.inl ⟨j, h, e⟩)
          (fun h => Or.inr (h ▸ e.symm)), fun h => h.elim (fun ⟨j, hj, e⟩ => ⟨j, by omega, e⟩)
          (fun e => ⟨i, by omega, e.symm⟩)⟩
      unfold sqP4Body
      exec_block
      · rw [r00, h10]; omega
      · config_simp; rw [r03, h10]; omega
      · config_simp; rw [r14, r00, h10, mL]; omega
      · config_simp; rw [r02, r00, h10, mL]; omega
      · config_simp; rw [h10]; omega
      · refine ⟨⟨‹WordsBounded _ _›, by config_simp; rw [h10, r1], by config_simp; exact h01',
          fun r a b c' e g => ?_, fun y hy => ?_, fun y hy => ?_, fun a ha hb => ?_⟩, by omega⟩
        · simp only [upd_apply, a, b, c', e, g, ite_false]; exact hq r a b c' e g
        · simp only
          rw [r02, r00, h10, mL, r14, r03, mV, r0, upd_other _ _ _ (by omega)]
          by_cases hyx : y = lv C i
          · subst hyx; rw [upd_same, iteT ((hnot _).2 (Or.inr rfl))]
          · rw [upd_other _ _ _ (by omega), hT y hy]
            by_cases h' : ∃ j < i, lv C j = y
            · rw [iteT h', iteT ((hnot _).2 (Or.inl h'))]
            · rw [iteF h', iteF (fun h'' => ((hnot _).1 h'').elim h' hyx)]
        · simp only
          rw [r02, r00, h10, mL, r14, r03, mV, r0]
          by_cases hyx : y = lv C i
          · subst hyx; rw [upd_same, iteT ((hnot _).2 (Or.inr rfl))]
          · rw [upd_other _ _ _ (by omega), upd_other _ _ _ (by omega), hF y hy]
            by_cases h' : ∃ j < i, lv C j = y
            · rw [iteT h', iteT ((hnot _).2 (Or.inl h'))]
            · rw [iteF h', iteF (fun h'' => ((hnot _).1 h'').elim h' hyx)]
        · simp only
          rw [r02, r00, h10, mL, r14, r03, mV, r0, upd_other _ _ _ (by omega),
            upd_other _ _ _ (by omega)]
          exact hfr a ha hb)
    (Nat.zero_le _) ⟨e0.wb_right, by config_simp, by config_simp; exact h1101,
      fun r h1 _ _ _ _ => by simp [h1], fun y _ => by simp, fun y _ => by simp,
      fun _ _ _ => rfl⟩
  obtain ⟨hw₁, -, -, hq₁, hT₁, hF₁, hfr₁⟩ := h₁
  refine ⟨d₁, _, .seq e0 e₁, hw₁, fun y hy => ?_, fun y hy => ?_, hfr₁,
    fun r a b c' e g => by rw [hq₁ r a b c' e g], by omega⟩
  · rw [hT₁ y hy]
    by_cases h : y ∈ UN C
    · rw [iteT ((lv_mem_iff C).2 h), iteT h]
    · rw [iteF (fun h' => h ((lv_mem_iff C).1 h')), iteF h]
  · rw [hF₁ y hy]
    by_cases h : y ∈ UN C
    · rw [iteT ((lv_mem_iff C).2 h), iteT h]
    · rw [iteF (fun h' => h ((lv_mem_iff C).1 h')), iteF h]

/-! ### The new marks -/

/-- The new mark of `u = U[i]` moved from the flag array to the marks, the flag cleared. -/
def sqP6Body : Stmt := block [.addN 1211 1200 1210, .loadN 1212 1211, .addN 1211 1202 1212,
  .loadN 1217 1211, .storeN 1211 0, .addN 1211 1019 1212, .storeN 1211 1217,
  .addN 1210 1210 1001]

/-- **The new marks** of `U`. -/
def sqP6 : Stmt := .seq (.instr (.constN 1210 0)) (.whileLtN 1210 1201 sqP6Body)

theorem sqP6_exec {d : Config} (hw : WordsBounded W d) {a0 aF aM : ℕ}
    (h01 : d.nreg 1001 = 1) (h0 : d.nreg 0 = 0) (h00 : d.nreg 1200 = a0)
    (h02 : d.nreg 1202 = aF) (h19 : d.nreg 1019 = aM) (h1201 : d.nreg 1201 = #U)
    (hU : ∀ l < #U, d.nmem (a0 + l) = lv U l)
    (l1 : aM + N ≤ a0) (l2 : a0 + N ≤ aF) (l3 : aF + N ≤ W) :
    ∃ d' k, Exec P W sqP6 d d' k ∧ WordsBounded W d' ∧
      (∀ y < N, d'.nmem (aM + y) = if y ∈ UN U then d.nmem (aF + y) else d.nmem (aM + y)) ∧
      (∀ y < N, d'.nmem (aF + y) = if y ∈ UN U then 0 else d.nmem (aF + y)) ∧
      (∀ a, (a < aM ∨ aM + N ≤ a) → (a < aF ∨ aF + N ≤ a) → d'.nmem a = d.nmem a) ∧
      (∀ r, r ≠ 1210 → r ≠ 1211 → r ≠ 1212 → r ≠ 1217 → d'.nreg r = d.nreg r) ∧
      k ≤ 10 * #U + 3 := by
  have hUN := card_le_N U
  let I : ℕ → Config → Prop := fun i d' => WordsBounded W d' ∧ d'.nreg 1210 = i ∧
    d'.nreg 1201 = #U ∧
    (∀ r, r ≠ 1210 → r ≠ 1211 → r ≠ 1212 → r ≠ 1217 → d'.nreg r = d.nreg r) ∧
    (∀ y < N, d'.nmem (aM + y) =
      if ∃ j < i, lv U j = y then d.nmem (aF + y) else d.nmem (aM + y)) ∧
    (∀ y < N, d'.nmem (aF + y) = if ∃ j < i, lv U j = y then 0 else d.nmem (aF + y)) ∧
    (∀ a, (a < aM ∨ aM + N ≤ a) → (a < aF ∨ aF + N ≤ a) → d'.nmem a = d.nmem a)
  have e0 := Exec.constN (P := P) hw 1210 0 (Nat.zero_le _)
  obtain ⟨d₁, k₁, e₁, h₁, hk₁⟩ := Exec.forN (P := P) (W := W) (ri := 1210) (rN := 1201)
    (N := #U) (lo := 0) (B := 8) (body := sqP6Body) I (fun i d' h => ⟨h.1, h.2.1, h.2.2.1⟩)
    (fun i d' h hi => by
      obtain ⟨hw', h10, h01', hq, hM, hF, hfr⟩ := h
      have hx := lv_ltN U hi
      have r00 : d'.nreg 1200 = a0 := by
        rw [hq 1200 (by omega) (by omega) (by omega) (by omega), h00]
      have r02 : d'.nreg 1202 = aF := by
        rw [hq 1202 (by omega) (by omega) (by omega) (by omega), h02]
      have r19 : d'.nreg 1019 = aM := by
        rw [hq 1019 (by omega) (by omega) (by omega) (by omega), h19]
      have r1 : d'.nreg 1001 = 1 := by
        rw [hq 1001 (by omega) (by omega) (by omega) (by omega), h01]
      have r0 : d'.nreg 0 = 0 := by
        rw [hq 0 (by omega) (by omega) (by omega) (by omega), h0]
      have mU : d'.nmem (a0 + i) = lv U i := by
        rw [hfr _ (Or.inr (by omega)) (Or.inl (by omega))]; exact hU i hi
      have hnew : ¬ ∃ j < i, lv U j = lv U i := fun ⟨j, hj, e⟩ => by
        have := lv_inj' U (by omega) hi e; omega
      have mF : d'.nmem (aF + lv U i) = d.nmem (aF + lv U i) := by
        rw [hF _ hx, iteF hnew]
      have hnot : ∀ y, (∃ j < i + 1, lv U j = y) ↔ (∃ j < i, lv U j = y) ∨ y = lv U i :=
        fun y => ⟨fun ⟨j, hj, e⟩ => (Nat.lt_succ_iff_lt_or_eq.1 hj).elim (fun h => Or.inl ⟨j, h, e⟩)
          (fun h => Or.inr (h ▸ e.symm)), fun h => h.elim (fun ⟨j, hj, e⟩ => ⟨j, by omega, e⟩)
          (fun e => ⟨i, by omega, e.symm⟩)⟩
      unfold sqP6Body
      exec_block
      · rw [r00, h10]; omega
      · config_simp; rw [r02, r00, h10, mU]; omega
      · config_simp; rw [r19, r00, h10, mU]; omega
      · config_simp; rw [h10]; omega
      · refine ⟨⟨‹WordsBounded _ _›, by config_simp; rw [h10, r1], by config_simp; exact h01',
          fun r a b c' e => ?_, fun y hy => ?_, fun y hy => ?_, fun a ha hb => ?_⟩, by omega⟩
        · simp only [upd_apply, a, b, c', e, ite_false]; exact hq r a b c' e
        · simp only
          rw [r02, r00, h10, mU, r19, r0, mF]
          by_cases hyx : y = lv U i
          · subst hyx; rw [upd_same, iteT ((hnot _).2 (Or.inr rfl))]
          · rw [upd_other _ _ _ (by omega), upd_other _ _ _ (by omega), hM y hy]
            by_cases h' : ∃ j < i, lv U j = y
            · rw [iteT h', iteT ((hnot _).2 (Or.inl h'))]
            · rw [iteF h', iteF (fun h'' => ((hnot _).1 h'').elim h' hyx)]
        · simp only
          rw [r02, r00, h10, mU, r19, r0, mF, upd_other _ _ _ (by omega)]
          by_cases hyx : y = lv U i
          · subst hyx; rw [upd_same, iteT ((hnot _).2 (Or.inr rfl))]
          · rw [upd_other _ _ _ (by omega), hF y hy]
            by_cases h' : ∃ j < i, lv U j = y
            · rw [iteT h', iteT ((hnot _).2 (Or.inl h'))]
            · rw [iteF h', iteF (fun h'' => ((hnot _).1 h'').elim h' hyx)]
        · simp only
          rw [r02, r00, h10, mU, r19, r0, mF, upd_other _ _ _ (by omega),
            upd_other _ _ _ (by omega)]
          exact hfr a ha hb)
    (Nat.zero_le _) ⟨e0.wb_right, by config_simp, by config_simp; exact h1201,
      fun r h1 _ _ _ => by simp [h1], fun y _ => by simp, fun y _ => by simp,
      fun _ _ _ => rfl⟩
  obtain ⟨hw₁, -, -, hq₁, hM₁, hF₁, hfr₁⟩ := h₁
  refine ⟨d₁, _, .seq e0 e₁, hw₁, fun y hy => ?_, fun y hy => ?_, hfr₁,
    fun r a b c' e => by rw [hq₁ r a b c' e], by omega⟩
  · rw [hM₁ y hy]
    by_cases h : y ∈ UN U
    · rw [iteT ((lv_mem_iff U).2 h), iteT h]
    · rw [iteF (fun h' => h ((lv_mem_iff U).1 h')), iteF h]
  · rw [hF₁ y hy]
    by_cases h : y ∈ UN U
    · rw [iteT ((lv_mem_iff U).2 h), iteT h]
    · rw [iteF (fun h' => h ((lv_mem_iff U).1 h')), iteF h]

/-! ### The vertices of `U` next to the separator -/

/-- The dart `g` (`1213`): `1217` set to `0` if the mark of its head is `0`. -/
def sqP5Dart : Stmt :=
  .seq (block [.addN 1211 1012 1213, .loadN 1215 1211, .addN 1211 1011 1215, .loadN 1215 1211,
    .addN 1211 1019 1215, .loadN 1216 1211])
    (.seq (.ifLtN 1216 1001 (.instr (.constN 1217 0)) .skip) (.instr (.addN 1213 1213 1001)))

theorem sqP5Dart_exec {d : Config} (hw : WordsBounded W d) {aT aR aM g : ℕ}
    (h01 : d.nreg 1001 = 1) (h11 : d.nreg 1011 = aT) (h12 : d.nreg 1012 = aR)
    (h19 : d.nreg 1019 = aM) (h13 : d.nreg 1213 = g) (hg : g < nD G)
    (hrv : d.nmem (aR + g) = rvG G g) (htl : d.nmem (aT + rvG G g) = tlG G (rvG G g))
    (hz : tlG G (rvG G g) < N) (b1 : aR + nD G ≤ W) (b2 : aT + nD G ≤ W) (b3 : aM + N ≤ W) :
    ∃ d' k, Exec P W sqP5Dart d d' k ∧ WordsBounded W d' ∧ d'.nreg 1213 = g + 1 ∧
      d'.nreg 1217 = (if d.nmem (aM + tlG G (rvG G g)) = 0 then 0 else d.nreg 1217) ∧
      (∀ r, r ≠ 1211 → r ≠ 1213 → r ≠ 1215 → r ≠ 1216 → r ≠ 1217 → d'.nreg r = d.nreg r) ∧
      d'.nmem = d.nmem ∧ k = 9 := by
  have hrl := rvG_lt (G := G) hg
  refine spec_seq ?_
  exec_block
  · rw [h12, h13]; omega
  · config_simp; rw [h11, h12, h13, hrv]; omega
  · config_simp; rw [h19, h11, h12, h13, hrv, htl]; omega
  · refine spec_seq ?_
    by_cases h0 : d.nmem (aM + tlG G (rvG G g)) = 0
    · refine spec_ifLtN_true (by config_simp; rw [h19, h11, h12, h13, hrv, htl, h0, h01]; omega) ?_
      refine spec_instr (Exec.constN ‹_› _ _ (Nat.zero_le _)) fun hw₁ => ?_
      refine spec_instr (Exec.addN hw₁ _ _ _ (by config_simp; rw [h13]; omega)) fun hw₂ => ?_
      refine ⟨hw₂, by config_simp; rw [h13, h01], by config_simp; rw [iteT h0],
        fun r a b c e f => ?_, rfl, rfl⟩
      simp only [upd_apply, a, b, c, e, f, ite_false]
    · refine spec_ifLtN_false (by config_simp; rw [h19, h11, h12, h13, hrv, htl, h01]; omega) ?_
      refine spec_skip ‹_› ?_
      refine spec_instr (Exec.addN ‹_› _ _ _ (by config_simp; rw [h13]; omega)) fun hw₂ => ?_
      refine ⟨hw₂, by config_simp; rw [h13, h01], by config_simp; rw [iteF h0],
        fun r a b c e f => ?_, rfl, rfl⟩
      simp only [upd_apply, a, b, c, e, ite_false]

open scoped Classical in
/-- The darts of one vertex `u < N`: `1217` set to `0` if a neighbour has the mark `0`. -/
theorem sqP5Darts_exec {d : Config} {a0 aF aM u : ℕ} (hL : FLay G W d a0 aF) (hu : u < N)
    (h19 : d.nreg 1019 = aM) (hM : aM + N ≤ W) (mk : ℕ → ℕ)
    (hmk : ∀ x < N, d.nmem (aM + x) = mk x)
    (h13 : d.nreg 1213 = gofs G u) (h14 : d.nreg 1214 = gofs G (u + 1)) :
    ∃ d' k, Exec P W (.whileLtN 1213 1214 sqP5Dart) d d' k ∧ WordsBounded W d' ∧
      d'.nreg 1217 = (if ∃ x, adjN G u x ∧ mk x = 0 then 0 else d.nreg 1217) ∧
      (∀ r, r ≠ 1211 → r ≠ 1213 → r ≠ 1215 → r ≠ 1216 → r ≠ 1217 → d'.nreg r = d.nreg r) ∧
      d'.nmem = d.nmem ∧ k ≤ 11 * dg G u + 2 := by
  have hmono := gofs_mono (G := G) u (u + 1) (Nat.le_succ _) hu
  have hND := gofs_le G (u + 1)
  have := hL.l0; have := hL.l1; have := hL.l2; have := hL.lB; have := hL.lF
  let J : ℕ → Config → Prop := fun g d' => WordsBounded W d' ∧ gofs G u ≤ g ∧
    d'.nreg 1213 = g ∧ d'.nreg 1214 = gofs G (u + 1) ∧
    (∀ r, r ≠ 1211 → r ≠ 1213 → r ≠ 1215 → r ≠ 1216 → r ≠ 1217 → d'.nreg r = d.nreg r) ∧
    d'.nreg 1217 = (if ∃ g', gofs G u ≤ g' ∧ g' < g ∧ mk (tlG G (rvG G g')) = 0 then 0
      else d.nreg 1217) ∧ d'.nmem = d.nmem
  obtain ⟨d₁, k₁, e₁, h₁, hk₁⟩ := Exec.forN (P := P) (W := W) (ri := 1213) (rN := 1214)
    (N := gofs G (u + 1)) (lo := gofs G u) (B := 9) (body := sqP5Dart) J
    (fun g d' h => ⟨h.1, h.2.2.1, h.2.2.2.1⟩)
    (fun g d' h hg => by
      obtain ⟨hw', hlo, h13', h14', hq, h17, hm⟩ := h
      have hgD : g < nD G := lt_of_lt_of_le hg hND
      obtain ⟨hzN, -⟩ := adjN_head hu hlo hg
      have k5 : ∀ r, r ≠ 1211 → r ≠ 1213 → r ≠ 1215 → r ≠ 1216 → r ≠ 1217 →
        d'.nreg r = d.nreg r := hq
      have r01 : d'.nreg 1001 = 1 := by
        rw [k5 1001 (by omega) (by omega) (by omega) (by omega) (by omega)]; exact hL.one
      have r11 := k5 1011 (by omega) (by omega) (by omega) (by omega) (by omega)
      have r12 := k5 1012 (by omega) (by omega) (by omega) (by omega) (by omega)
      have r19 : d'.nreg 1019 = aM := by
        rw [k5 1019 (by omega) (by omega) (by omega) (by omega) (by omega)]; exact h19
      have hrl := rvG_lt (G := G) hgD
      obtain ⟨d₂, k₂, e₂, hw₂, c13, c17, q₂, m₂, hk₂⟩ := sqP5Dart_exec (P := P) hw' r01 r11 r12
        r19 h13' hgD (by rw [hm]; exact hL.rv g hgD) (by rw [hm]; exact hL.tl _ hrl) hzN
        (by omega) (by omega) hM
      refine ⟨d₂, k₂, e₂, ⟨hw₂, by omega, c13, by
        rw [q₂ 1214 (by omega) (by omega) (by omega) (by omega) (by omega)]; exact h14',
        fun r a b c e f => by rw [q₂ r a b c e f, hq r a b c e f], ?_, by rw [m₂, hm]⟩,
        by omega⟩
      rw [c17, hm, hmk _ hzN, h17]
      by_cases h0 : mk (tlG G (rvG G g)) = 0
      · rw [iteT h0, iteT ⟨g, hlo, by omega, h0⟩]
      · rw [iteF h0]
        by_cases h' : ∃ g', gofs G u ≤ g' ∧ g' < g ∧ mk (tlG G (rvG G g')) = 0
        · obtain ⟨g', h1, h2, h3⟩ := h'
          rw [iteT ⟨g', h1, h2, h3⟩, iteT ⟨g', h1, by omega, h3⟩]
        · rw [iteF h', iteF (fun ⟨g', h1, h2, h3⟩ => by
            rcases Nat.lt_succ_iff_lt_or_eq.1 h2 with h2 | rfl
            · exact h' ⟨g', h1, h2, h3⟩
            · exact h0 h3)])
    hmono ⟨hL.wb, le_rfl, h13, h14, fun r _ _ _ _ _ => rfl, by
      rw [iteF (fun ⟨g', h1, h2, _⟩ => by omega)], rfl⟩
  obtain ⟨hw₁, -, -, -, hq₁, h17₁, hm₁⟩ := h₁
  refine ⟨d₁, k₁, e₁, hw₁, ?_, hq₁, hm₁, by unfold dg; omega⟩
  rw [h17₁]
  have e : (∃ g', gofs G u ≤ g' ∧ g' < gofs G (u + 1) ∧ mk (tlG G (rvG G g')) = 0) ↔
      ∃ x, adjN G u x ∧ mk x = 0 := by
    constructor
    · rintro ⟨g', h1, h2, h3⟩; exact ⟨_, (adjN_head hu h1 h2).2, h3⟩
    · rintro ⟨x, hx, h0⟩
      obtain ⟨g', h1, h2, rfl⟩ := exists_dart_adjN hx
      exact ⟨g', h1, h2, h0⟩
  by_cases h : ∃ x, adjN G u x ∧ mk x = 0
  · rw [iteT (e.2 h), iteT h]
  · rw [iteF (fun h' => h (e.1 h')), iteF h]

variable (G) in
open scoped Classical in
/-- The new mark of `u`: `0` if a neighbour has the mark `0`, else the mark of `u`. -/
noncomputable def nm (mk : ℕ → ℕ) (u : ℕ) : ℕ :=
  if ∃ x, adjN G u x ∧ mk x = 0 then 0 else mk u

/-- The vertex `u = U[i]`: its new mark into the flag array. -/
def sqP5Body : Stmt :=
  .seq (block [.addN 1211 1200 1210, .loadN 1212 1211, .addN 1211 1019 1212, .loadN 1217 1211,
    .addN 1211 1010 1212, .loadN 1213 1211, .addN 1211 1211 1001, .loadN 1214 1211])
    (.seq (.whileLtN 1213 1214 sqP5Dart)
      (block [.addN 1211 1202 1212, .storeN 1211 1217, .addN 1210 1210 1001]))

/-- **The new marks of `U`** into the flag array. -/
def sqP5 : Stmt := .seq (.instr (.constN 1210 0)) (.whileLtN 1210 1201 sqP5Body)

theorem sqP5_exec {d : Config} {a0 aF aM : ℕ} (hL : FLay G W d a0 aF)
    (h19 : d.nreg 1019 = aM) (hM : aM + N ≤ a0)
    (h1201 : d.nreg 1201 = #U) (hU : ∀ l < #U, d.nmem (a0 + l) = lv U l) :
    ∃ d' k, Exec P W sqP5 d d' k ∧ WordsBounded W d' ∧
      (∀ r, r < 1210 ∨ 1217 < r → d'.nreg r = d.nreg r) ∧
      (∀ y < N, d'.nmem (aF + y) =
        if y ∈ UN U then nm G (fun x => d.nmem (aM + x)) y else d.nmem (aF + y)) ∧
      (∀ a, (a < aF ∨ aF + N ≤ a) → d'.nmem a = d.nmem a) ∧
      k ≤ 11 * ∑ v ∈ U, G.degree v + 15 * #U + 3 := by
  have hUN := card_le_N U
  have := hL.l0; have := hL.l1; have := hL.l2; have := hL.lB; have := hL.lF
  set mk : ℕ → ℕ := fun x => d.nmem (aM + x) with hmk
  let I : ℕ → Config → Prop := fun i d' => WordsBounded W d' ∧ d'.nreg 1210 = i ∧
    d'.nreg 1201 = #U ∧ (∀ r, r < 1210 ∨ 1217 < r → d'.nreg r = d.nreg r) ∧
    (∀ y < N, d'.nmem (aF + y) = if ∃ j < i, lv U j = y then nm G mk y else d.nmem (aF + y)) ∧
    (∀ a, (a < aF ∨ aF + N ≤ a) → d'.nmem a = d.nmem a)
  have e0 := Exec.constN (P := P) hL.wb 1210 0 (Nat.zero_le _)
  obtain ⟨d₁, k₁, e₁, h₁, hk₁⟩ := sqForN (P := P) (W := W) (ri := 1210) (rN := 1201)
    (M := #U) (lo := 0) (body := sqP5Body) (fun i => 11 * dg G (lv U i) + 13) I
    (fun i d' h => ⟨h.1, h.2.1, h.2.2.1⟩)
    (fun i d' h hi => by
      obtain ⟨hw', h10, h01', hq, hF', hfr⟩ := h
      have hL' := hL.mono hw' (fun r hr => hq r (Or.inl (by omega))) hfr
      have hu := lv_ltN U hi
      have mU : d'.nmem (a0 + i) = lv U i := by rw [hfr _ (Or.inl (by omega))]; exact hU i hi
      have r10 : d'.nreg 1010 = d.nreg 1010 := hq 1010 (Or.inl (by omega))
      have r19 : d'.nreg 1019 = aM := by rw [hq 1019 (Or.inl (by omega))]; exact h19
      have mO : ∀ v ≤ N, d'.nmem (d.nreg 1010 + v) = gofs G v := fun v hv => by
        rw [← r10]; exact hL'.ofs v hv
      have mM : ∀ x < N, d'.nmem (aM + x) = mk x := fun x hx => by
        rw [hfr _ (Or.inl (by omega))]
      obtain ⟨d₂, k₂, e₂, hw₂, c12, c17, c13, c14, q₂, m₂, hk₂⟩ : ∃ d₂ k₂, Exec P W
          (block [.addN 1211 1200 1210, .loadN 1212 1211, .addN 1211 1019 1212, .loadN 1217 1211,
          .addN 1211 1010 1212, .loadN 1213 1211, .addN 1211 1211 1001, .loadN 1214 1211])
          d' d₂ k₂ ∧ WordsBounded W d₂ ∧ d₂.nreg 1212 = lv U i ∧ d₂.nreg 1217 = mk (lv U i) ∧
          d₂.nreg 1213 = gofs G (lv U i) ∧ d₂.nreg 1214 = gofs G (lv U i + 1) ∧
          (∀ r, r ≠ 1211 → r ≠ 1212 → r ≠ 1213 → r ≠ 1214 → r ≠ 1217 → d₂.nreg r = d'.nreg r) ∧
          d₂.nmem = d'.nmem ∧ k₂ = 8 := by
        have hw := hw'
        exec_block
        · rw [hL'.h00, h10]; omega
        · config_simp; rw [r19, hL'.h00, h10, mU]; omega
        · config_simp; rw [r10, hL'.h00, h10, mU]; omega
        · config_simp; rw [r10, hL'.h00, h10, mU, hL'.one]; omega
        · refine ⟨‹_›, ?_, ?_, ?_, ?_, fun r a b c e f => ?_, rfl, rfl⟩
          · config_simp; rw [hL'.h00, h10, mU]
          · config_simp; rw [r19, hL'.h00, h10, mU, mM _ hu]
          · config_simp; rw [r10, hL'.h00, h10, mU, mO _ hu.le]
          · config_simp; rw [r10, hL'.h00, h10, mU, hL'.one, Nat.add_assoc, mO _ hu]
          · simp only [upd_apply, a, b, c, e, f, ite_false]
      have q2 : ∀ r, r < 1210 → r ≠ 1212 → r ≠ 1213 → r ≠ 1214 → r ≠ 1211 →
          d₂.nreg r = d'.nreg r := fun r h1 h2 h3 h4 h5 => q₂ r h5 h2 h3 h4 (by omega)
      have hL₂ := hL'.mono hw₂ (fun r hr => q₂ r (by omega) (by omega) (by omega) (by omega)
        (by omega)) (fun a _ => by rw [m₂])
      obtain ⟨d₃, k₃, e₃, hw₃, c17', q₃, m₃, hk₃⟩ := sqP5Darts_exec (P := P) (aM := aM) hL₂ hu
        (by rw [q₂ 1019 (by omega) (by omega) (by omega) (by omega) (by omega)]; exact r19)
        (by omega) mk (fun x hx => by rw [m₂]; exact mM x hx) c13 c14
      have k3 : ∀ r, r ≠ 1211 → r ≠ 1213 → r ≠ 1215 → r ≠ 1216 → r ≠ 1217 →
          r ≠ 1212 → r ≠ 1214 → d₃.nreg r = d'.nreg r := fun r a b c e f g h =>
        by rw [q₃ r a b c e f, q₂ r a g b h f]
      have s02 : d₃.nreg 1202 = aF := by
        rw [k3 1202 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
        exact hL'.h02
      have s12 : d₃.nreg 1212 = lv U i := by
        rw [q₃ 1212 (by omega) (by omega) (by omega) (by omega) (by omega)]; exact c12
      have s10 : d₃.nreg 1210 = i := by
        rw [k3 1210 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
        exact h10
      have s01 : d₃.nreg 1001 = 1 := by
        rw [k3 1001 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
        exact hL'.one
      have s17 : d₃.nreg 1217 = nm G mk (lv U i) := by
        rw [c17', c17]; rfl
      obtain ⟨d₄, k₄, e₄, hw₄, c10, q₄, m₄, hk₄⟩ : ∃ d₄ k₄, Exec P W
          (block [.addN 1211 1202 1212, .storeN 1211 1217, .addN 1210 1210 1001]) d₃ d₄ k₄ ∧
          WordsBounded W d₄ ∧ d₄.nreg 1210 = i + 1 ∧
          (∀ r, r ≠ 1210 → r ≠ 1211 → d₄.nreg r = d₃.nreg r) ∧
          d₄.nmem = upd d₃.nmem (aF + lv U i) (nm G mk (lv U i)) ∧ k₄ = 3 := by
        have hw := hw₃
        exec_block
        · rw [s02, s12]; omega
        · config_simp; rw [s10, s01]; omega
        · refine ⟨‹_›, by config_simp; rw [s10, s01], fun r a b => ?_, ?_, rfl⟩
          · simp only [upd_apply, a, b, ite_false]
          · config_simp; rw [s02, s12, s17]
      have hnot : ∀ y, (∃ j < i + 1, lv U j = y) ↔ (∃ j < i, lv U j = y) ∨ y = lv U i :=
        fun y => ⟨fun ⟨j, hj, e⟩ => (Nat.lt_succ_iff_lt_or_eq.1 hj).elim (fun h => Or.inl ⟨j, h, e⟩)
          (fun h => Or.inr (h ▸ e.symm)), fun h => h.elim (fun ⟨j, hj, e⟩ => ⟨j, by omega, e⟩)
          (fun e => ⟨i, by omega, e.symm⟩)⟩
      refine ⟨d₄, _, .seq e₂ (.seq e₃ e₄), ⟨hw₄, c10, ?_, fun r hr => ?_, fun y hy => ?_,
        fun a ha => ?_⟩, by omega⟩
      · rw [q₄ 1201 (by omega) (by omega), k3 1201 (by omega) (by omega) (by omega) (by omega)
          (by omega) (by omega) (by omega)]; exact h01'
      · rw [q₄ r (by omega) (by omega), k3 r (by omega) (by omega) (by omega) (by omega)
          (by omega) (by omega) (by omega)]; exact hq r hr
      · rw [m₄, m₃, m₂]
        by_cases hyx : y = lv U i
        · subst hyx; rw [upd_same, iteT ((hnot _).2 (Or.inr rfl))]
        · rw [upd_other _ _ _ (by omega), hF' y hy]
          by_cases h' : ∃ j < i, lv U j = y
          · rw [iteT h', iteT ((hnot _).2 (Or.inl h'))]
          · rw [iteF h', iteF (fun h'' => ((hnot _).1 h'').elim h' hyx)]
      · rw [m₄, m₃, m₂, upd_other _ _ _ (by omega)]; exact hfr a ha)
    (Nat.zero_le _) ⟨e0.wb_right, by config_simp, by config_simp; exact h1201,
      fun r hr => by config_simp; rw [upd_other _ _ _ (by omega)],
      fun y hy => by simp, fun _ _ => rfl⟩
  obtain ⟨hw₁, -, -, hq₁, hF₁, hfr₁⟩ := h₁
  refine ⟨d₁, _, .seq e0 e₁, hw₁, fun r hr => by rw [hq₁ r hr], fun y hy => ?_, hfr₁, ?_⟩
  · rw [hF₁ y hy]
    by_cases h : y ∈ UN U
    · rw [iteT ((lv_mem_iff U).2 h), iteT h]
    · rw [iteF (fun h' => h ((lv_mem_iff U).1 h')), iteF h]
  · simp only [Nat.add_assoc] at hk₁; rw [sum_dg_lv] at hk₁; omega

/-! ### The program and the facts behind it -/

/-- **The separator routine of the square on the machine.** -/
def squareProg : Stmt :=
  .seq (.seq sqP1 (.seq sqP2 sqP3)) (.seq compSepProg (.seq sqP4 (.seq sqP5 sqP6)))

theorem compSepProg_wmax : compSepProg.wmax < 1200 := by decide +kernel

/-- The new marks are the marks of the separation of the square. -/
theorem nm_spec {mk : ℕ → ℕ} {S A B : Finset (Fin N)} (hS : S ⊆ closedNbhd G U)
    (hmk : ∀ v ∈ closedNbhd G U, (mk v = 0 ↔ v ∈ S) ∧ (mk v = 1 ↔ v ∈ A) ∧ (mk v = 2 ↔ v ∈ B))
    {v : Fin N} (hv : v ∈ U) :
    (nm G mk v = 0 ↔ v ∈ U ∩ closedNbhd G S) ∧
      (nm G mk v = 1 ↔ v ∈ (A ∩ U) \ closedNbhd G S) ∧
      (nm G mk v = 2 ↔ v ∈ (B ∩ U) \ closedNbhd G S) := by
  have hv' : v ∈ closedNbhd G U := subset_closedNbhd U hv
  have key : nm G mk v = 0 ↔ v ∈ closedNbhd G S := by
    unfold nm
    constructor
    · intro h
      split_ifs at h with hex
      · obtain ⟨x, ⟨hvN, hxN, hadj⟩, hx0⟩ := hex
        have hxU' : (⟨x, hxN⟩ : Fin N) ∈ closedNbhd G U := mem_closedNbhd_of_adj hv hadj
        exact mem_closedNbhd_of_adj (((hmk _ hxU').1).1 hx0) hadj.symm
      · exact subset_closedNbhd S (((hmk v hv').1).1 h)
    · intro h
      obtain ⟨s, hs, hsv⟩ := mem_biUnion.1 h
      rcases mem_insert.1 hsv with e | e
      · subst e
        split_ifs
        · rfl
        · exact ((hmk v hv').1).2 hs
      · have hadj : G.Adj s v := (G.mem_neighborFinset _ _).1 e
        split_ifs with hex
        · rfl
        · exact absurd ⟨(s : ℕ), ⟨v.2, s.2, hadj.symm⟩, ((hmk s (hS hs)).1).2 hs⟩ hex
  have hne : ∀ {j : ℕ}, j ≠ 0 → nm G mk v = j → v ∉ closedNbhd G S := fun hj h h' => by
    rw [← key] at h'; omega
  have hval : nm G mk v ≠ 0 → nm G mk v = mk v := fun h0 => by
    unfold nm at h0 ⊢
    split_ifs at h0 ⊢
    · exact absurd rfl h0
    · rfl
  refine ⟨by rw [key, mem_inter]; exact ⟨fun h => ⟨hv, h⟩, fun h => h.2⟩, ⟨fun h => ?_, fun h => ?_⟩,
    ⟨fun h => ?_, fun h => ?_⟩⟩
  · have h0 : nm G mk v ≠ 0 := by rw [h]; omega
    have hn := hne one_ne_zero h
    rw [hval h0] at h
    exact mem_sdiff.2 ⟨mem_inter.2 ⟨((hmk v hv').2.1).1 h, hv⟩, hn⟩
  · obtain ⟨hAU, hn⟩ := mem_sdiff.1 h
    rw [hval (fun h0 => hn (key.1 h0))]
    exact ((hmk v hv').2.1).2 (mem_inter.1 hAU).1
  · have h0 : nm G mk v ≠ 0 := by rw [h]; omega
    have hn := hne two_ne_zero h
    rw [hval h0] at h
    exact mem_sdiff.2 ⟨mem_inter.2 ⟨((hmk v hv').2.2).1 h, hv⟩, hn⟩
  · obtain ⟨hAU, hn⟩ := mem_sdiff.1 h
    rw [hval (fun h0 => hn (key.1 h0))]
    exact ((hmk v hv').2.2).2 (mem_inter.1 hAU).1

/-- The weights during the separator of the components: those of `U`, zero on the rest of the
closed neighbourhood. -/
def wSq (G : SimpleGraph (Fin N)) [DecidableRel G.Adj] (U : Finset (Fin N)) (w : Fin N → ℕ) :
    Fin N → ℕ :=
  fun v => if v ∈ closedNbhd G U ∧ v ∉ U then 0 else w v

theorem sum_wSq : ∑ v ∈ closedNbhd G U, wSq G U w v = ∑ v ∈ U, w v := by
  rw [← sum_subset (subset_closedNbhd U) (fun v hv hvU => by simp [wSq, hv, hvU])]
  exact sum_congr rfl fun v hv => by simp [wSq, hv]

theorem wI_wSq {y : ℕ} (hy : y < N) : SepProg.wI (wSq G U w) y =
    if y ∈ UN (closedNbhd G U) ∧ y ∉ UN U then 0 else SepProg.wI w y := by
  have e : ∀ C : Finset (Fin N), y ∈ UN C ↔ (⟨y, hy⟩ : Fin N) ∈ C := fun C => by
    rw [mem_UN]; exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨hy, h⟩⟩
  simp [SepProg.wI, hy, e, wSq]

theorem compSep_wSq (R : Kasteleyn.RotationSystem G) :
    compSep G (ltComp R (ord N)) (ord N) (closedNbhd G U) (wSq G U w) =
      compSep G (ltComp R (ord N)) (ord N) (closedNbhd G U) (fun v => if v ∈ U then w v else 0) :=
  compSep_congr R (ord N) mem_ord fun v hv => by
    by_cases h : v ∈ U
    · simp [wSq, h]
    · simp [wSq, h, hv]

/-- The registers kept by the separator of the square. -/
def KeptS (r : ℕ) : Prop :=
  r < 1000 ∨ r = 1001 ∨ (1010 ≤ r ∧ r ≤ 1015) ∨ (1017 ≤ r ∧ r ≤ 1019) ∨ r = 1100 ∨
    (1102 ≤ r ∧ r ≤ 1105) ∨ (1200 ≤ r ∧ r ≤ 1204)

variable (G) in
/-- **The state after the separator of the square**: the kept registers, the marks `0`, `1`, `2`
of the three parts of `sq` on `U`, the memory as at the start except the marks of the closed
neighbourhood, the list area at `1100`, the areas at `1015`, `1103` and the save area. -/
structure SDone (w : Fin N → ℕ) (U : Finset (Fin N)) (W : ℕ)
    (sq : Finset (Fin N) × Finset (Fin N) × Finset (Fin N)) (c d : Config) : Prop where
  wb : WordsBounded W d
  regs : ∀ r, KeptS r → d.nreg r = c.nreg r
  mark : ∀ v ∈ U, (d.nmem (c.nreg 1019 + v) = 0 ↔ v ∈ sq.1) ∧
    (d.nmem (c.nreg 1019 + v) = 1 ↔ v ∈ sq.2.1) ∧ (d.nmem (c.nreg 1019 + v) = 2 ↔ v ∈ sq.2.2)
  frame : ∀ a, (∀ v ∈ closedNbhd G U, a ≠ c.nreg 1019 + v) →
    (a < c.nreg 1100 ∨ c.nreg 1100 + N ≤ a) → (a < c.nreg 1015 ∨ c.nreg 1015 + N ≤ a) →
    (a < c.nreg 1103 ∨ c.nreg 1103 + N ≤ a) → (a < c.nreg 1203 ∨ c.nreg 1203 + N ≤ a) →
    d.nmem a = c.nmem a
  out : d.output = c.output
  rr : d.rreg = c.rreg
  rm : d.rmem = c.rmem

/-! ### The run -/

/-- The flags and the bucket pass: from `SPre` to `CPre` for the closed neighbourhood and the
weights `wSq`. -/
theorem sqFront_exec {R : Kasteleyn.RotationSystem G} {Z : ℕ} {c : Config}
    (hs : SPre G R w U Z W c) :
    ∃ d k, Exec P W (.seq sqP1 (.seq sqP2 sqP3)) c d k ∧
      CPre G R (wSq G U w) (closedNbhd G U) Z W d ∧
      (∀ r, r < 1205 → r ≠ 1101 → d.nreg r = c.nreg r) ∧
      (∀ l < #(closedNbhd G U),
        d.nmem (c.nreg 1203 + l) = SepProg.wI w (lv (closedNbhd G U) l)) ∧
      (∀ x < N, d.nmem (c.nreg 1202 + x) =
        if x ∈ UN U then 2 else if x ∈ UN (closedNbhd G U) then 1 else 0) ∧
      (∀ a, (a < c.nreg 1100 ∨ (c.nreg 1100 + N ≤ a ∧ a < c.nreg 1014) ∨
        (c.nreg 1014 + N ≤ a ∧ a < c.nreg 1202) ∨ (c.nreg 1202 + N ≤ a ∧ a < c.nreg 1203) ∨
        c.nreg 1203 + N ≤ a) → d.nmem a = c.nmem a) ∧
      d.output = c.output ∧ d.rreg = c.rreg ∧ d.rmem = c.rmem ∧
      k ≤ 15 * N + 11 * ∑ v ∈ U, G.degree v + 18 * #U + 11 := by
  have := hs.lU; have := hs.lC; have := hs.lQ; have := hs.lW; have := hs.lS; have := hs.l0
  have := hs.l1; have := hs.l2; have := hs.l3; have := hs.l4; have := hs.l5; have := hs.l6
  have := hs.l7; have := hs.lA; have := hs.lB; have := hs.lF; have := hs.lV; have := hs.lZ
  have hNW : N + 2 ≤ W := by omega
  obtain ⟨d₁, k₁, e₁, hw₁, h05₁, hF₁, hfr₁, hq₁, hk₁⟩ := sqP1_exec (P := P) (U := U) hs.wb hNW
    hs.one rfl rfl hs.uu hs.ul (by omega) (by omega)
  have hLc : FLay G W c (c.nreg 1200) (c.nreg 1202) := ⟨hs.wb, hs.one, rfl, rfl, hs.l0, hs.l1,
    by omega, hs.lB, by omega, hs.ofs, hs.tl, hs.rv⟩
  have hL₁ := hLc.mono hw₁ (fun r hr => hq₁ r (by omega) (by omega) (by omega) (by omega)) hfr₁
  obtain ⟨d₂, k₂, e₂, hw₂, hq₂, hF₂, hfr₂, hk₂⟩ := sqP2_exec (P := P) (U := U) hL₁ hNW
    (by rw [hq₁ 1201 (by omega) (by omega) (by omega) (by omega)]; exact hs.uu)
    (fun l hl => by rw [hfr₁ _ (Or.inl (by have := card_le_N U; omega))]; exact hs.ul l hl)
    (fun x hx => by rw [hF₁ x hx, hs.fz x hx])
  obtain ⟨d₃, k₃, e₃, hw₃, h01₃, hq₃, hL₃, hV₃, hT₃, hfr₃, hk₃⟩ := sqP3_exec (P := P) hs hw₂
    (fun r hr => by rw [hq₂ r (Or.inl (by omega)), hq₁ r (by omega) (by omega) (by omega)
      (by omega)])
    (by rw [hq₂ 1205 (Or.inl (by omega))]; exact h05₁) hF₂
    (fun a ha => by rw [hfr₂ a ha, hfr₁ a ha])
  have R3 : ∀ r, r < 1205 → r ≠ 1101 → d₃.nreg r = c.nreg r := fun r h1 h2 => by
    rw [hq₃ r h2 (by omega) (by omega) (by omega) (by omega) (by omega), hq₂ r (Or.inl (by omega)),
      hq₁ r (by omega) (by omega) (by omega) (by omega)]
  have M3 : ∀ a, (a < c.nreg 1100 ∨ (c.nreg 1100 + N ≤ a ∧ a < c.nreg 1014) ∨
      (c.nreg 1014 + N ≤ a ∧ a < c.nreg 1202) ∨ (c.nreg 1202 + N ≤ a ∧ a < c.nreg 1203) ∨
      c.nreg 1203 + N ≤ a) → d₃.nmem a = c.nmem a :=
    fun a ha => by rw [hfr₃ a (by omega) (by omega) (by omega), hfr₂ a (by omega), hfr₁ a (by omega)]
  have e : Exec P W (.seq sqP1 (.seq sqP2 sqP3)) c d₃ _ := .seq e₁ (.seq e₂ e₃)
  have rr := Exec.real_of_noReal e (by decide)
  have g := fun r (h1 : r < 1205) (h2 : r ≠ 1101) => R3 r h1 h2
  have hU'N := card_le_N (closedNbhd G U)
  have lay : CLay G (closedNbhd G U) (wSq G U w) W d₃ := {
    wb := hw₃
    one := by rw [g 1001 (by omega) (by omega)]; exact hs.one
    r0 := by rw [g 0 (by omega) (by omega)]; exact hs.r0
    uu := h01₃
    lU := by rw [g 1100 (by omega) (by omega), g 1102 (by omega) (by omega)]; exact hs.lU
    lC := by rw [g 1102 (by omega) (by omega), g 1103 (by omega) (by omega)]; exact hs.lC
    lQ := by rw [g 1103 (by omega) (by omega), g 1104 (by omega) (by omega)]; exact hs.lQ
    lW := by rw [g 1104 (by omega) (by omega), g 1105 (by omega) (by omega)]; exact hs.lW
    lS := by rw [g 1105 (by omega) (by omega), g 1010 (by omega) (by omega)]; exact hs.lS
    l0 := by rw [g 1010 (by omega) (by omega), g 1011 (by omega) (by omega)]; exact hs.l0
    l1 := by rw [g 1011 (by omega) (by omega), g 1012 (by omega) (by omega)]; exact hs.l1
    l2 := by rw [g 1012 (by omega) (by omega), g 1013 (by omega) (by omega)]; exact hs.l2
    l3 := by rw [g 1013 (by omega) (by omega), g 1014 (by omega) (by omega)]; exact hs.l3
    l4 := by rw [g 1014 (by omega) (by omega), g 1015 (by omega) (by omega)]; exact hs.l4
    l5 := by rw [g 1015 (by omega) (by omega), g 1017 (by omega) (by omega)]; exact hs.l5
    l6 := by rw [g 1017 (by omega) (by omega), g 1018 (by omega) (by omega)]; exact hs.l6
    l7 := by rw [g 1018 (by omega) (by omega), g 1019 (by omega) (by omega)]; exact hs.l7
    l8 := by rw [g 1019 (by omega) (by omega)]; omega
    ul := fun l hl => by rw [g 1100 (by omega) (by omega)]; exact hL₃ l hl
    ofs := fun v hv => by
      rw [g 1010 (by omega) (by omega), M3 _ (Or.inr (Or.inl ⟨by omega, by omega⟩))]; exact hs.ofs v hv
    tl := fun j hj => by
      rw [g 1011 (by omega) (by omega), M3 _ (Or.inr (Or.inl ⟨by omega, by omega⟩))]; exact hs.tl j hj
    rv := fun j hj => by
      rw [g 1012 (by omega) (by omega), M3 _ (Or.inr (Or.inl ⟨by omega, by omega⟩))]; exact hs.rv j hj
    wt := fun v hv => by rw [g 1014 (by omega) (by omega), hT₃ v hv, wI_wSq hv]
    cid := fun x hx => by
      rw [g 1102 (by omega) (by omega), M3 _ (Or.inr (Or.inl ⟨by omega, by omega⟩))]; exact hs.cid x hx
    cw := fun j hj => by
      rw [g 1104 (by omega) (by omega), M3 _ (Or.inr (Or.inl ⟨by omega, by omega⟩))]; exact hs.cw j hj
    sn := fun j hj => by
      rw [g 1105 (by omega) (by omega), M3 _ (Or.inr (Or.inl ⟨by omega, by omega⟩))]; exact hs.sn j hj
    sw := by rw [sum_wSq]; exact hs.sw }
  refine ⟨d₃, _, e, {
    lay := lay
    ro := fun j hj => by
      rw [g 1013 (by omega) (by omega), M3 _ (Or.inr (Or.inl ⟨by omega, by omega⟩))]; exact hs.ro j hj
    lab := fun x hx => by
      rw [g 1017 (by omega) (by omega), M3 _ (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩)))]
      exact hs.lab x hx
    rk := fun j hj => by
      rw [g 1018 (by omega) (by omega), M3 _ (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩)))]
      exact hs.rk j hj
    lZ := by rw [g 1100 (by omega) (by omega)]; exact hs.lZ
    zero := fun a ha => by rw [M3 _ (Or.inl (by omega))]; exact hs.zero a ha
    zreg := fun r hr => by rw [g r (by omega) (by omega)]; exact hs.zreg r hr
    rz := fun r hr => by rw [rr.1]; exact hs.rz r hr
    rmz := fun a ha => by rw [rr.2]; exact hs.rmz a ha
    big := by rw [sum_wSq]; exact hs.big }, R3, hV₃, fun x hx => ?_, M3,
    Exec.output_of_ou e (by decide), rr.1, rr.2, by omega⟩
  rw [hfr₃ _ (Or.inr (by omega)) (Or.inl (by omega)) (Or.inr (by omega))]; exact hF₂ x hx

/-- **The separator routine of the square on the machine**: from `SPre` (a plane rotation system
`R` of `G` of maximum degree at most `Δ`, the sorted list of `U`), `squareProg` runs to the state
`SDone` with the marks `0`, `1`, `2` of the three parts of
`((ltRoutine R hR (ord N) mem_ord).square hΔ).sep U w` on `U`, within
`15 N + 2411 #U' + (6 Δ + 3415) ∑_{U'} deg + 12 ∑_U w + 43 #U + 22 ∑_U deg + 5420` steps,
`U' = closedNbhd G U`. -/
theorem squareProg_exec {R : Kasteleyn.RotationSystem G} (hR : R.IsPlane) {Δ : ℕ}
    (hΔ : ∀ v, G.degree v ≤ Δ) {Z : ℕ} {c : Config} (hs : SPre G R w U Z W c) :
    ∃ d k, Exec P W squareProg c d k ∧
      k ≤ 15 * N + 2411 * #(closedNbhd G U) +
        (6 * Δ + 3415) * ∑ v ∈ closedNbhd G U, G.degree v + 12 * ∑ v ∈ U, w v +
        43 * #U + 22 * ∑ v ∈ U, G.degree v + 5420 ∧
      SDone G w U W (((ltRoutine R hR (ord N) mem_ord).square hΔ).sep U w) c d := by
  have := hs.lU; have := hs.lC; have := hs.lQ; have := hs.lW; have := hs.lS; have := hs.l0
  have := hs.l1; have := hs.l2; have := hs.l3; have := hs.l4; have := hs.l5; have := hs.l6
  have := hs.l7; have := hs.lA; have := hs.lB; have := hs.lF; have := hs.lV
  have hNW : N + 2 ≤ W := by omega
  have hUN := card_le_N U
  have hU'N := card_le_N (closedNbhd G U)
  obtain ⟨d₃, k₃, e₃, hpre, R3, hV₃, hF₃, M3, ou₃, rr₃, rm₃, hk₃⟩ := sqFront_exec (P := P) hs
  obtain ⟨d₄, k₄, e₄, hk₄, hD⟩ := compSepProg_exec (P := P) hR hΔ hpre
  rw [sum_wSq] at hk₄
  have hi4 : ∀ r, 1200 ≤ r → d₄.nreg r = d₃.nreg r := fun r hr =>
    Exec.nreg_of_wr e₄ (Stmt.wr_of_wmax (by have := compSepProg_wmax; omega))
  have K4 : ∀ r, KeptS r → d₄.nreg r = c.nreg r := fun r hr => by
    unfold KeptS at hr
    by_cases h : 1200 ≤ r
    · rw [hi4 r h, R3 r (by omega) (by omega)]
    · rw [hD.regs r (by unfold KeptC; omega), R3 r (by omega) (by omega)]
  have h1101₄ : d₄.nreg 1101 = #(closedNbhd G U) := by
    rw [hD.regs 1101 (by unfold KeptC; omega)]; exact hpre.lay.uu
  have F4 := hD.frame
  rw [R3 1019 (by omega) (by omega), R3 1015 (by omega) (by omega),
    R3 1103 (by omega) (by omega)] at F4
  have hmk := hD.mark
  rw [R3 1019 (by omega) (by omega)] at hmk
  have kS : ∀ r, KeptS r → r < 1210 ∧ r ≠ 1101 ∧ r ≠ 1205 := fun r hr => by
    unfold KeptS at hr; omega
  -- restoring the weights
  obtain ⟨d₅, k₅, e₅, hw₅, hT₅, hFl₅, hfr₅, hq₅, hk₅⟩ := sqP4_exec (P := P)
    (C := closedNbhd G U) (SepProg.wI w) hD.wb (aL := c.nreg 1100) (aV := c.nreg 1203)
    (aT := c.nreg 1014) (aF := c.nreg 1202)
    (by rw [K4 1001 (by unfold KeptS; omega)]; exact hs.one)
    (by rw [K4 0 (by unfold KeptS; omega)]; exact hs.r0)
    (K4 1100 (by unfold KeptS; omega)) (K4 1203 (by unfold KeptS; omega))
    (K4 1014 (by unfold KeptS; omega)) (K4 1202 (by unfold KeptS; omega)) h1101₄
    (fun l hl => by
      rw [F4 _ (fun v _ => by have := v.2; omega) (Or.inl (by omega)) (Or.inl (by omega))]
      have := hpre.lay.ul l hl
      rwa [R3 1100 (by omega) (by omega)] at this)
    (fun l hl => by
      rw [F4 _ (fun v _ => by have := v.2; omega) (Or.inr (by omega)) (Or.inr (by omega))]
      exact hV₃ l hl)
    (by omega) (by omega) (by omega) (by omega)
  have K5 : ∀ r, KeptS r → d₅.nreg r = c.nreg r := fun r hr => by
    have := kS r hr
    rw [hq₅ r (by omega) (by omega) (by omega) (by omega) (by omega), K4 r hr]
  have hF5 : ∀ y < N, d₅.nmem (c.nreg 1202 + y) = 0 := fun y hy => by
    rw [hFl₅ y hy]
    by_cases h : y ∈ UN (closedNbhd G U)
    · rw [iteT h]
    · rw [iteF h, F4 _ (fun v _ => by have := v.2; omega) (Or.inr (by omega))
        (Or.inr (by omega)), hF₃ y hy, iteF (fun h' => h (mem_UN_cl.2 (Or.inl h'))), iteF h]
  have G5 : ∀ a, c.nreg 1019 ≤ a → a < c.nreg 1202 →
      (∀ v ∈ closedNbhd G U, a ≠ c.nreg 1019 + v) → d₅.nmem a = d₃.nmem a := fun a h1 h2 h3 => by
    rw [hfr₅ a (Or.inr (by omega)) (Or.inl h2), F4 a h3 (Or.inr (by omega)) (Or.inr (by omega))]
  have H5 : ∀ a, c.nreg 1105 + N + 1 ≤ a → a < c.nreg 1014 → d₅.nmem a = c.nmem a :=
    fun a h1 h2 => by
      rw [hfr₅ a (Or.inl h2) (Or.inl (by omega)),
        F4 a (fun v _ => by have := v.2; omega) (Or.inl (by omega)) (Or.inr (by omega)),
        M3 a (Or.inr (Or.inl ⟨by omega, h2⟩))]
  have hU5 : ∀ l < #U, d₅.nmem (c.nreg 1200 + l) = lv U l := fun l hl => by
    rw [G5 _ (by omega) (by omega) (fun v _ => by have := v.2; omega),
      M3 _ (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩)))]
    exact hs.ul l hl
  -- the new marks
  have hL₅ : FLay G W d₅ (c.nreg 1200) (c.nreg 1202) := ⟨hw₅,
    by rw [K5 1001 (by unfold KeptS; omega)]; exact hs.one,
    K5 1200 (by unfold KeptS; omega), K5 1202 (by unfold KeptS; omega),
    by rw [K5 1010 (by unfold KeptS; omega), K5 1011 (by unfold KeptS; omega)]; exact hs.l0,
    by rw [K5 1011 (by unfold KeptS; omega), K5 1012 (by unfold KeptS; omega)]; exact hs.l1,
    by rw [K5 1012 (by unfold KeptS; omega)]; omega, by omega, by omega,
    fun v hv => by
      rw [K5 1010 (by unfold KeptS; omega), H5 _ (by omega) (by omega)]; exact hs.ofs v hv,
    fun j hj => by
      rw [K5 1011 (by unfold KeptS; omega), H5 _ (by omega) (by omega)]; exact hs.tl j hj,
    fun j hj => by
      rw [K5 1012 (by unfold KeptS; omega), H5 _ (by omega) (by omega)]; exact hs.rv j hj⟩
  obtain ⟨d₆, k₆, e₆, hw₆, hq₆, hF₆, hfr₆, hk₆⟩ := sqP5_exec (P := P) (U := U) hL₅
    (K5 1019 (by unfold KeptS; omega)) (by omega)
    (by rw [K5 1201 (by unfold KeptS; omega)]; exact hs.uu) hU5
  have K6 : ∀ r, KeptS r → d₆.nreg r = c.nreg r := fun r hr => by
    have := kS r hr
    rw [hq₆ r (Or.inl (by omega)), K5 r hr]
  obtain ⟨d₇, k₇, e₇, hw₇, hM₇, hF₇, hfr₇, hq₇, hk₇⟩ := sqP6_exec (P := P) (U := U) hw₆
    (by rw [K6 1001 (by unfold KeptS; omega)]; exact hs.one)
    (by rw [K6 0 (by unfold KeptS; omega)]; exact hs.r0)
    (K6 1200 (by unfold KeptS; omega)) (K6 1202 (by unfold KeptS; omega))
    (K6 1019 (by unfold KeptS; omega))
    (by rw [K6 1201 (by unfold KeptS; omega)]; exact hs.uu)
    (fun l hl => by rw [hfr₆ _ (Or.inl (by omega))]; exact hU5 l hl)
    (by omega) (by omega) (by omega)
  have e : Exec P W squareProg c d₇ _ := .seq e₃ (.seq e₄ (.seq e₅ (.seq e₆ e₇)))
  have rr₅ := Exec.real_of_noReal e₅ (by decide)
  have rr₆ := Exec.real_of_noReal e₆ (by decide)
  have rr₇ := Exec.real_of_noReal e₇ (by decide)
  refine ⟨d₇, _, e, by omega, ⟨hw₇, fun r hr => ?_, fun v hv => ?_, fun a h1 h2 h3 h4 h5 => ?_,
    ?_, ?_, ?_⟩⟩
  · have := kS r hr
    rw [hq₇ r (by omega) (by omega) (by omega) (by omega), K6 r hr]
  · -- the marks
    set U' := closedNbhd G U
    set w' : Fin N → ℕ := fun v => if v ∈ U then w v else 0
    have hsep := (ltRoutine R hR (ord N) mem_ord).isSeparation U' w'
    have hS : (compSep G (ltComp R (ord N)) (ord N) U' w').1 ⊆ U' := fun x hx =>
      hsep.union_eq ▸ mem_union_left _ (mem_union_left _ hx)
    have hval : d₇.nmem (c.nreg 1019 + v) = nm G (fun x => d₅.nmem (c.nreg 1019 + x)) v := by
      rw [hM₇ v v.2, iteT (val_mem_UN.2 hv), hF₆ v v.2, iteT (val_mem_UN.2 hv)]
    have hm := nm_spec (G := G) (U := U) (mk := fun x => d₅.nmem (c.nreg 1019 + x))
      (A := (compSep G (ltComp R (ord N)) (ord N) U' w').2.1)
      (B := (compSep G (ltComp R (ord N)) (ord N) U' w').2.2) hS (fun x hx => by
        have h := hmk x hx
        rw [compSep_wSq] at h
        rw [hfr₅ _ (Or.inr (by omega)) (Or.inl (by have := x.2; omega))]
        exact h) hv
    rw [hval]
    exact hm
  · -- the frame
    by_cases hMr : c.nreg 1019 ≤ a ∧ a < c.nreg 1019 + N
    · obtain ⟨y, rfl⟩ : ∃ y, a = c.nreg 1019 + y := ⟨a - c.nreg 1019, by omega⟩
      have hyN : y < N := by omega
      have hyU' : y ∉ UN (closedNbhd G U) := fun h => by
        obtain ⟨_, hm⟩ := mem_UN.1 h
        exact h1 _ hm rfl
      have hyU : y ∉ UN U := fun h => hyU' (mem_UN_cl.2 (Or.inl h))
      rw [hM₇ y hyN, iteF hyU, hfr₆ _ (Or.inl (by omega)), G5 _ (by omega) (by omega) h1,
        M3 _ (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩)))]
    by_cases hFr : c.nreg 1202 ≤ a ∧ a < c.nreg 1202 + N
    · obtain ⟨y, rfl⟩ : ∃ y, a = c.nreg 1202 + y := ⟨a - c.nreg 1202, by omega⟩
      have hyN : y < N := by omega
      rw [hs.fz y hyN, hF₇ y hyN]
      by_cases hyU : y ∈ UN U
      · rw [iteT hyU]
      · rw [iteF hyU, hF₆ y hyN, iteF hyU, hF5 y hyN]
    have e67 : d₇.nmem a = d₅.nmem a := by
      rw [hfr₇ a (by omega) (by omega), hfr₆ a (by omega)]
    by_cases hTr : c.nreg 1014 ≤ a ∧ a < c.nreg 1014 + N
    · obtain ⟨y, rfl⟩ : ∃ y, a = c.nreg 1014 + y := ⟨a - c.nreg 1014, by omega⟩
      have hyN : y < N := by omega
      rw [e67, hT₅ y hyN, hs.wt y hyN]
      by_cases hy : y ∈ UN (closedNbhd G U)
      · rw [iteT hy]
      · rw [iteF hy, F4 _ (fun v _ => by have := v.2; omega) (Or.inl (by omega))
          (Or.inr (by omega))]
        have := hpre.lay.wt y hyN
        rw [R3 1014 (by omega) (by omega), wI_wSq hyN, iteF (fun h => hy h.1)] at this
        exact this
    · rw [e67, hfr₅ a (by omega) (by omega), F4 a h1 h3 h4, M3 a (by omega)]
  · rw [Exec.output_of_ou e₇ (by decide), Exec.output_of_ou e₆ (by decide),
      Exec.output_of_ou e₅ (by decide), hD.out, ou₃]
  · rw [rr₇.1, rr₆.1, rr₅.1, hD.rr, rr₃]
  · rw [rr₇.2, rr₆.2, rr₅.2, hD.rm, rm₃]

/-- The step bound of `squareProg_exec` in terms of `#U` and `Δ`. -/
theorem squareProg_cost_le {Δ : ℕ} (hΔ : ∀ v, G.degree v ≤ Δ) :
    15 * N + 2411 * #(closedNbhd G U) +
        (6 * Δ + 3415) * ∑ v ∈ closedNbhd G U, G.degree v + 12 * ∑ v ∈ U, w v +
        43 * #U + 22 * ∑ v ∈ U, G.degree v + 5420 ≤
      15 * N + ((Δ + 1) * (6 * Δ ^ 2 + 3415 * Δ + 2411) + 22 * Δ + 43) * #U +
        12 * ∑ v ∈ U, w v + 5420 := by
  have h1 : ∑ v ∈ closedNbhd G U, G.degree v ≤ #(closedNbhd G U) * Δ := by
    simpa using sum_le_card_nsmul (closedNbhd G U) _ Δ (fun v _ => hΔ v)
  have h3 : ∑ v ∈ U, G.degree v ≤ #U * Δ := by
    simpa using sum_le_card_nsmul U _ Δ (fun v _ => hΔ v)
  have h2 := card_closedNbhd_le hΔ U
  nlinarith [Nat.mul_le_mul_left (6 * Δ + 3415) h1,
    Nat.mul_le_mul_left (6 * Δ ^ 2 + 3415 * Δ + 2411) h2, Nat.mul_le_mul_left 22 h3]

end Piece

end PlanarSeparator
