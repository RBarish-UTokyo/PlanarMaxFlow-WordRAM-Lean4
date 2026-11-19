module

public import PlanarSeparator.Machine.CompBFS

/-!
# The components of a vertex set on the machine

The first two passes of the program computing `PlanarSeparator.compSep` for a vertex set `U`
of a graph `G` on `Fin N` held in global arrays (`CLay`): the sorted list of `U` at `aU`
(register `1100`, length `#U` in `1101`), the label array `aCid` (`1102`), the queue `aQ`
(`1103`), the component weights `aCw` (`1104`), the seen flags `aSn` (`1105`), below the offsets,
tails, reversals, rotation and weights of `PlanarSeparator.Piece.Pre`. The scratch registers are
`[1110, 1200)`; register `0` holds `0`.

* `initA`, **`initA_exec`**: the labels `1` on `U` and the weight of `U` in `1120`.
* `compsB`, **`compsB_exec`**: breadth-first search from every vertex of `U` still labelled `1`,
  in the order of the list; at the end the labels and weights satisfy `BInv` with all of `U`
  scanned, within `9 #U + 40 #U + 15 ∑_{v ∈ U} deg v + 4` steps.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarSeparator

namespace Piece

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

/-! ### The programs -/

/-- **The labels `1` on `U`** and the weight of `U` in `1120`. -/
def initA : Stmt :=
  .seq (block [.constN 1110 0, .constN 1120 0, .constN 1130 2])
    (.whileLtN 1110 1101 (block [.addN 1118 1100 1110, .loadN 1114 1118, .addN 1118 1102 1114,
      .storeN 1118 1001, .addN 1118 1014 1114, .loadN 1119 1118, .addN 1120 1120 1119,
      .addN 1110 1110 1001]))

/-- A new vertex `z` (`1117`, its label cell in `1118`) gets the label `1121` and joins the queue. -/
def bNew : Stmt := block [.storeN 1118 1121, .addN 1118 1103 1113, .storeN 1118 1117,
  .addN 1113 1113 1001]

/-- The dart `g` (`1115`): its head `z`, labelled if its label is `1`. -/
def bDart : Stmt :=
  .seq (block [.addN 1118 1012 1115, .loadN 1119 1118, .addN 1118 1011 1119, .loadN 1117 1118,
    .addN 1118 1102 1117, .loadN 1119 1118])
    (.seq (.ifLtN 0 1119 (.ifLtN 1119 1130 bNew .skip) .skip) (.instr (.addN 1115 1115 1001)))

/-- The next vertex `x` of the queue: its weight, then its darts. -/
def bVert : Stmt :=
  .seq (block [.addN 1118 1103 1112, .loadN 1114 1118, .addN 1112 1112 1001,
    .addN 1118 1014 1114, .loadN 1119 1118, .addN 1122 1122 1119, .addN 1118 1010 1114,
    .loadN 1115 1118, .addN 1118 1118 1001, .loadN 1116 1118])
    (.whileLtN 1115 1116 bDart)

/-- The search from `x` (`1114`, its label cell in `1118`) with a new label. -/
def bSearch : Stmt :=
  .seq (block [.addN 1111 1111 1001, .addN 1121 1111 1001, .storeN 1118 1121, .storeN 1103 1114,
    .constN 1112 0, .copyN 1113 1001, .constN 1122 0])
    (.seq (.whileLtN 1112 1113 bVert) (block [.addN 1118 1104 1111, .storeN 1118 1122]))

/-- The `i`-th vertex of the list: a search if it is labelled `1`. -/
def bOuter : Stmt :=
  .seq (block [.addN 1118 1100 1110, .loadN 1114 1118, .addN 1118 1102 1114, .loadN 1119 1118])
    (.seq (.ifLtN 1119 1130 bSearch .skip) (.instr (.addN 1110 1110 1001)))

/-- **The components of `U`.** -/
def compsB : Stmt :=
  .seq (block [.constN 1110 0, .constN 1111 0]) (.whileLtN 1110 1101 bOuter)

/-! ### Register frames -/

/-- The scratch registers `[1110, 1200)`. -/
def cscr (r : ℕ) : Bool := 1110 ≤ r && r < 1200

theorem keep_of_cscr {P : Input} {W : ℕ} {s : Stmt} {c c' : Config} {t : ℕ}
    (e : Exec P W s c c' t) (hs : swok cscr s = true) {r : ℕ} (hr : r < 1110) :
    c'.nreg r = c.nreg r :=
  Exec.nreg_of_wr e (wr_of_swok (by simp [cscr]; omega) hs)

/-! ### The layout -/

variable {N : ℕ} (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]

/-- **The layout of the program of the components**: the list of `U`, the label, queue, weight
and seen arrays (the latter three zero), then the global arrays of `Pre`. -/
structure CLay (U : Finset (Fin N)) (w : Fin N → ℕ) (W : ℕ) (c : Config) : Prop where
  wb : WordsBounded W c
  one : c.nreg 1001 = 1
  r0 : c.nreg 0 = 0
  uu : c.nreg 1101 = #U
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
  l8 : c.nreg 1019 + N ≤ W
  ul : ∀ l < #U, c.nmem (c.nreg 1100 + l) = lv U l
  ofs : ∀ v ≤ N, c.nmem (c.nreg 1010 + v) = gofs G v
  tl : ∀ g < nD G, c.nmem (c.nreg 1011 + g) = tlG G g
  rv : ∀ g < nD G, c.nmem (c.nreg 1012 + g) = rvG G g
  wt : ∀ v < N, c.nmem (c.nreg 1014 + v) = SepProg.wI w v
  cid : ∀ x < N, c.nmem (c.nreg 1102 + x) = 0
  cw : ∀ j ≤ N, c.nmem (c.nreg 1104 + j) = 0
  sn : ∀ j ≤ N, c.nmem (c.nreg 1105 + j) = 0
  sw : 6 * ∑ v ∈ U, w v ≤ W

variable {G} {U : Finset (Fin N)} {w : Fin N → ℕ} {W : ℕ} {P : Input}

theorem card_le_N (U : Finset (Fin N)) : #U ≤ N := by
  simpa using card_le_univ U

theorem lv_ltN (U : Finset (Fin N)) {l : ℕ} (h : l < #U) : lv U l < N :=
  lv_lt U (by rw [length_clist_ord]; exact h)

theorem CLay.NW {c : Config} (hl : CLay G U w W c) : N + 2 ≤ W := by
  have := hl.l8; have := hl.lU; have := hl.lC; have := hl.lQ; have := hl.lW; have := hl.l0
  have := hl.lS; have := hl.l1; have := hl.l2; have := hl.l3; have := hl.l4; have := hl.l5
  have := hl.l6; have := hl.l7
  omega

theorem sum_UN (U : Finset (Fin N)) (w : Fin N → ℕ) :
    ∑ x ∈ UN U, SepProg.wI w x = ∑ v ∈ U, w v := by
  unfold UN
  rw [sum_map]
  refine sum_congr rfl fun v _ => ?_
  simp [SepProg.wI]

theorem lv_inj' (U : Finset (Fin N)) {i j : ℕ} (hi : i < #U) (hj : j < #U)
    (h : lv U i = lv U j) : i = j := by
  rw [← length_clist_ord] at hi hj
  rcases lt_trichotomy i j with hl | rfl | hl
  · have := lv_inc U i j hl hj; omega
  · rfl
  · have := lv_inc U j i hl hi; omega

theorem sum_lv_le (U : Finset (Fin N)) (f : ℕ → ℕ) {k : ℕ} (hk : k ≤ #U) :
    ∑ l ∈ range k, f (lv U l) ≤ ∑ x ∈ UN U, f x :=
  sum_range_leN (lv U) (UN U) (fun l _ => lv_mem_UN U (by omega))
    (fun a _ b _ h => lv_inj' U (by omega) (by omega) h) f

theorem sum_lv_eq (U : Finset (Fin N)) (f : ℕ → ℕ) :
    ∑ l ∈ range #U, f (lv U l) = ∑ x ∈ UN U, f x :=
  sum_range_eqN (lv U) (UN U) (fun l hl => lv_mem_UN U hl)
    (fun a ha b hb h => lv_inj' U ha hb h) (fun x hx => by
      obtain ⟨hxN, hxU⟩ := mem_UN.1 hx
      obtain ⟨l, hl, he⟩ := exists_ul U hxU
      refine ⟨l, by rw [← ul_length]; exact hl, ?_⟩
      rw [lv_ul U hl, he]) f

theorem lv_mem_iff (U : Finset (Fin N)) {x : ℕ} :
    (∃ j < #U, lv U j = x) ↔ x ∈ UN U := by
  constructor
  · rintro ⟨j, hj, rfl⟩; exact lv_mem_UN U hj
  · intro hx
    obtain ⟨hxN, hxU⟩ := mem_UN.1 hx
    obtain ⟨l, hl, he⟩ := exists_ul U hxU
    exact ⟨l, by rw [← ul_length]; exact hl, by rw [lv_ul U hl, he]⟩

/-! ### The labels `1` -/

theorem initA_exec {c : Config} (hl : CLay G U w W c) :
    ∃ d k, Exec P W initA c d k ∧ k ≤ 10 * #U + 5 ∧ WordsBounded W d ∧
      (∀ r < 1110, d.nreg r = c.nreg r) ∧ d.nreg 1130 = 2 ∧
      d.nreg 1120 = ∑ v ∈ U, w v ∧
      (∀ x < N, d.nmem (c.nreg 1102 + x) = if x ∈ UN U then 1 else 0) ∧
      (∀ a, a < c.nreg 1102 ∨ c.nreg 1102 + N ≤ a → d.nmem a = c.nmem a) := by
  have hNW := hl.NW
  have hU := card_le_N U
  have hsw := hl.sw
  have lU := hl.lU; have lC := hl.lC; have lQ := hl.lQ; have lW := hl.lW; have lS := hl.lS
  have l0 := hl.l0; have l1 := hl.l1; have l2 := hl.l2; have l3 := hl.l3; have l4 := hl.l4
  have l5 := hl.l5; have l6 := hl.l6; have l7 := hl.l7; have l8 := hl.l8
  set aC := c.nreg 1102
  let I : ℕ → Config → Prop := fun l d => WordsBounded W d ∧ d.nreg 1110 = l ∧
    d.nreg 1101 = #U ∧ (∀ r < 1110, d.nreg r = c.nreg r) ∧ d.nreg 1130 = 2 ∧
    d.nreg 1120 = ∑ j ∈ range l, SepProg.wI w (lv U j) ∧
    (∀ x < N, d.nmem (aC + x) = if ∃ j < l, lv U j = x then 1 else 0) ∧
    (∀ a, a < aC ∨ aC + N ≤ a → d.nmem a = c.nmem a)
  obtain ⟨d₀, k₀, e₀, h₀⟩ : ∃ d₀ k₀, Exec P W (block [.constN 1110 0, .constN 1120 0,
      .constN 1130 2]) c d₀ k₀ ∧ I 0 d₀ ∧ k₀ = 3 := by
    have hw := hl.wb
    exec_block
    · omega
    · omega
    · omega
    · refine ⟨⟨‹WordsBounded _ _›, ?_⟩, rfl⟩
      config_simp
      refine ⟨hl.uu, fun r hr => ?_, by simp, fun x hx => ?_, fun _ _ => trivial⟩
      · simp only [upd_apply]; split_ifs <;> omega
      · simp only [not_lt_zero, false_and, exists_false, ↓reduceIte]; exact hl.cid x hx
  obtain ⟨d₁, k₁, e₁, h₁, hk₁⟩ := Exec.forN (P := P) (W := W) (ri := 1110) (rN := 1101)
    (N := #U) (lo := 0) (B := 8) (body := block [.addN 1118 1100 1110, .loadN 1114 1118,
      .addN 1118 1102 1114, .storeN 1118 1001, .addN 1118 1014 1114, .loadN 1119 1118,
      .addN 1120 1120 1119, .addN 1110 1110 1001]) I (fun l d h => ⟨h.1, h.2.1, h.2.2.1⟩)
    (fun l d h hlt => by
      obtain ⟨hw, h10, h01, hfix, h30, h20, hlab, hfr⟩ := h
      have hx := lv_ltN U hlt
      have r00 : d.nreg 1100 = c.nreg 1100 := hfix 1100 (by omega)
      have r02 : d.nreg 1102 = aC := hfix 1102 (by omega)
      have r14 : d.nreg 1014 = c.nreg 1014 := hfix 1014 (by omega)
      have r1 : d.nreg 1001 = 1 := (hfix 1001 (by omega)).trans hl.one
      have mU : d.nmem (c.nreg 1100 + l) = lv U l := by
        rw [hfr _ (Or.inl (by omega))]; exact hl.ul l hlt
      have mW : d.nmem (c.nreg 1014 + lv U l) = SepProg.wI w (lv U l) := by
        rw [hfr _ (Or.inr (by omega))]
        exact hl.wt _ hx
      have hsum := sum_lv_le U (SepProg.wI w) (k := l + 1) (by omega)
      rw [sum_UN, sum_range_succ] at hsum
      exec_block
      · rw [r00, h10]; omega
      · config_simp; rw [r02, r00, h10, mU]; omega
      · config_simp; rw [r14, r00, h10, mU]; omega
      · config_simp
        rw [r02, r00, h10, mU, r14, upd_other _ _ _ (by omega), mW, h20]; omega
      · config_simp; rw [h10]; omega
      · refine ⟨⟨‹WordsBounded _ _›, ?_⟩, by omega⟩
        config_simp
        rw [r02, r00, h10, mU, r14, upd_other _ _ _ (by omega), mW, h20, r1, sum_range_succ]
        refine ⟨rfl, h01, fun r hr => ?_, h30, rfl, fun x hx => ?_, fun a ha => ?_⟩
        · simp only [upd_apply]; split_ifs <;> first | omega | exact hfix r hr
        · simp only [upd_apply]
          split_ifs with h1 h2 h2
          · rfl
          · exact absurd ⟨l, Nat.lt_succ_self _, by omega⟩ h2
          · obtain ⟨j, hj, hjx⟩ := h2
            rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
            · rw [hlab x hx, iteT ⟨j, hj, hjx⟩]
            · omega
          · rw [hlab x hx, iteF (fun ⟨j, hj, hjx⟩ => h2 ⟨j, by omega, hjx⟩)]
        · rw [upd_other _ _ _ (by omega)]; exact hfr a ha)
    (Nat.zero_le _) h₀.1
  obtain ⟨hw₁, -, -, hfix₁, h30₁, h20₁, hlab₁, hfr₁⟩ := h₁
  refine ⟨d₁, k₀ + k₁, .seq e₀ e₁, by omega, hw₁, hfix₁, h30₁, ?_, fun x hx => ?_, hfr₁⟩
  · rw [h20₁, sum_lv_eq U (SepProg.wI w), sum_UN]
  · rw [hlab₁ x hx]
    by_cases h : x ∈ UN U
    · rw [iteT ((lv_mem_iff U).2 h), iteT h]
    · rw [iteF (fun h' => h ((lv_mem_iff U).1 h')), iteF h]

/-! ### The state of the search -/

theorem rvG_lt {g : ℕ} (hg : g < nD G) : rvG G g < nD G := by
  obtain ⟨d, rfl⟩ := exists_dart_of_lt G hg
  rw [rvG_dartNum]; exact (dartNum G d.symm).2

/-- The cells written by the search: labels, queue, component weights. -/
def Wz (c : Config) (a : ℕ) : Prop :=
  (c.nreg 1102 ≤ a ∧ a < c.nreg 1102 + N) ∨ (c.nreg 1103 ≤ a ∧ a < c.nreg 1103 + N) ∨
    (c.nreg 1104 ≤ a ∧ a < c.nreg 1104 + N + 1)

variable (N) in
/-- **The environment of the search**: the registers below `1110` and `1130 = 2` kept, the
memory kept off the labels, the queue and the component weights. -/
structure Env (W : ℕ) (c d : Config) : Prop where
  wb : WordsBounded W d
  fix : ∀ r < 1110, d.nreg r = c.nreg r
  two : d.nreg 1130 = 2
  fr : ∀ a, ¬ Wz (N := N) c a → d.nmem a = c.nmem a

/-- The labels. -/
def labF (c d : Config) (x : ℕ) : ℕ := d.nmem (c.nreg 1102 + x)
/-- The queue. -/
def QF (c d : Config) (j : ℕ) : ℕ := d.nmem (c.nreg 1103 + j)
/-- The component weights. -/
def cwF (c d : Config) (j : ℕ) : ℕ := d.nmem (c.nreg 1104 + j)

variable (G) in
/-- **The state in the loop over the darts** of the vertex `x = Q h` of the search from `s` with
the label `cc`, at the dart `g`. -/
structure DI (U : Finset (Fin N)) (W : ℕ) (c : Config) (lab₀ cw₀ q₀ : ℕ → ℕ)
    (s cc h x i nc acc g : ℕ) (d : Config) : Prop where
  env : Env N W c d
  r15 : d.nreg 1115 = g
  r16 : d.nreg 1116 = gofs G (x + 1)
  r21 : d.nreg 1121 = cc
  r12 : d.nreg 1112 = h + 1
  r22 : d.nreg 1122 = acc
  r11 : d.nreg 1111 = nc + 1
  r10 : d.nreg 1110 = i
  qx : QF c d h = x
  core : BCore G U s cc lab₀ (labF c d) (QF c d) (d.nreg 1113)
  ht : h < d.nreg 1113
  proc : Proc G U cc h (labF c d) (QF c d)
  part : Part G U cc x g (labF c d)
  cw : ∀ j ≤ N, cwF c d j = cw₀ j
  pre : ∀ j ≤ h, QF c d j = q₀ j

theorem Wz_cid {c : Config} {a : ℕ} (h : ¬ Wz (N := N) c a)
    {x : ℕ} (hx : x < N) : a ≠ c.nreg 1102 + x := by
  rintro rfl; exact h (Or.inl ⟨by omega, by omega⟩)

theorem bDart_step {c : Config} (hl : CLay G U w W c) {lab₀ cw₀ q₀ : ℕ → ℕ}
    {s cc h x i nc acc g : ℕ} (hB : BInv G U w i nc lab₀ cw₀) (hcc : cc = nc + 2)
    (hs : s ∈ UN U) (hs1 : lab₀ s = 1) {d : Config}
    (hI : DI G U W c lab₀ cw₀ q₀ s cc h x i nc acc g d) (hg1 : gofs G x ≤ g)
    (hg2 : g < gofs G (x + 1)) :
    ∃ d' k, Exec P W bDart d d' k ∧ DI G U W c lab₀ cw₀ q₀ s cc h x i nc acc (g + 1) d' ∧
      k ≤ 13 := by
  obtain ⟨env, r15, r16, r21, r12, r22, r11, r10, qx, core, ht, proc, part, hcw, hpre⟩ := hI
  have lU := hl.lU; have lC := hl.lC; have lQ := hl.lQ; have lW := hl.lW; have lS := hl.lS
  have l0 := hl.l0; have l1 := hl.l1; have l2 := hl.l2; have l3 := hl.l3; have l4 := hl.l4
  have l5 := hl.l5; have l6 := hl.l6; have l7 := hl.l7; have l8 := hl.l8
  have hU := card_le_N U
  have f := env.fix
  have e12 : d.nreg 1012 = c.nreg 1012 := f 1012 (by omega)
  have e11 : d.nreg 1011 = c.nreg 1011 := f 1011 (by omega)
  have e02 : d.nreg 1102 = c.nreg 1102 := f 1102 (by omega)
  have e03 : d.nreg 1103 = c.nreg 1103 := f 1103 (by omega)
  have e01 : d.nreg 1001 = 1 := (f 1001 (by omega)).trans hl.one
  have e00 : d.nreg 0 = 0 := (f 0 (by omega)).trans hl.r0
  have hxN : x < N := qx ▸ core.lt_N ht
  have hgD : g < nD G := lt_of_lt_of_le hg2 (gofs_le G _)
  have hrv := rvG_lt (G := G) hgD
  obtain ⟨hzN, hadj⟩ := adjN_head (G := G) hxN hg1 hg2
  set z := tlG G (rvG G g) with hz
  have m1 : d.nmem (c.nreg 1012 + g) = rvG G g := by
    rw [env.fr _ (by unfold Wz; omega)]; exact hl.rv g hgD
  have m2 : d.nmem (c.nreg 1011 + rvG G g) = z := by
    rw [env.fr _ (by unfold Wz; omega)]; exact hl.tl _ hrv
  -- the first block
  obtain ⟨d₁, k₁, e₁, hw₁, a18, a19, a17, q₁, m₁, hk₁⟩ : ∃ d₁ k₁, Exec P W
      (block [.addN 1118 1012 1115, .loadN 1119 1118, .addN 1118 1011 1119, .loadN 1117 1118,
        .addN 1118 1102 1117, .loadN 1119 1118]) d d₁ k₁ ∧ WordsBounded W d₁ ∧
      d₁.nreg 1118 = c.nreg 1102 + z ∧ d₁.nreg 1119 = labF c d z ∧ d₁.nreg 1117 = z ∧
      (∀ r, r ≠ 1118 → r ≠ 1119 → r ≠ 1117 → d₁.nreg r = d.nreg r) ∧ d₁.nmem = d.nmem ∧
      k₁ = 6 := by
    have hw := env.wb
    exec_block
    · rw [e12, r15]; omega
    · config_simp; rw [e12, e11, r15, m1]; omega
    · config_simp; rw [e12, e11, e02, r15, m1, m2]; omega
    · refine ⟨‹WordsBounded _ _›, ?_⟩
      config_simp
      rw [e12, e11, e02, r15, m1, m2]
      refine ⟨rfl, rfl, rfl, fun r h1 h2 h3 => ?_⟩
      simp [h1, h2, h3]
  have b15 : d₁.nreg 1115 = g := by rw [q₁ 1115 (by omega) (by omega) (by omega), r15]
  have b01 : d₁.nreg 1001 = 1 := by rw [q₁ 1001 (by omega) (by omega) (by omega), e01]
  -- the end: the next dart
  have hlast : ∀ d₂ : Config, WordsBounded W d₂ → d₂.nreg 1115 = g → d₂.nreg 1001 = 1 →
      ∃ d₃, Exec P W (.instr (.addN 1115 1115 1001)) d₂ d₃ 1 ∧ d₃.nreg 1115 = g + 1 ∧
        (∀ r, r ≠ 1115 → d₃.nreg r = d₂.nreg r) ∧ d₃.nmem = d₂.nmem ∧ WordsBounded W d₃ := by
    intro d₂ hw₂ h15 h01
    have e := Exec.addN (P := P) hw₂ 1115 1115 1001 (by rw [h15, h01]; omega)
    refine ⟨_, e, by simp [h15, h01], fun r hr => by simp [hr], rfl, e.wb_right⟩
  -- the old cases
  have hold : labF c d z ≠ 1 → ∀ d₂ k₂, Exec P W (.ifLtN 0 1119 (.ifLtN 1119 1130 bNew .skip) .skip)
      d₁ d₂ k₂ → d₂ = d₁ → k₂ ≤ 3 →
      ∃ d' k, Exec P W bDart d d' k ∧ DI G U W c lab₀ cw₀ q₀ s cc h x i nc acc (g + 1) d' ∧
        k ≤ 13 := by
    intro hne d₂ k₂ e₂ hd₂ hk₂
    subst hd₂
    obtain ⟨d₃, e₃, h15, q₃, m₃, hw₃⟩ := hlast d₂ hw₁ b15 b01
    have qq : ∀ r, r ≠ 1118 → r ≠ 1119 → r ≠ 1117 → r ≠ 1115 → d₃.nreg r = d.nreg r :=
      fun r a b c' e => by rw [q₃ r e, q₁ r a b c']
    have mm : d₃.nmem = d.nmem := by rw [m₃, m₁]
    have hlab : labF c d₃ = labF c d := by unfold labF; rw [mm]
    have hQ : QF c d₃ = QF c d := by unfold QF; rw [mm]
    have h13 : d₃.nreg 1113 = d.nreg 1113 := qq 1113 (by omega) (by omega) (by omega) (by omega)
    refine ⟨d₃, k₁ + (k₂ + 1), .seq e₁ (.seq e₂ e₃), ⟨⟨hw₃, fun r hr => by
      rw [qq r (by omega) (by omega) (by omega) (by omega)]; exact f r hr,
      by rw [qq 1130 (by omega) (by omega) (by omega) (by omega)]; exact env.two,
      fun a ha => by rw [mm]; exact env.fr a ha⟩, h15, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, fun j hj => by rw [hQ]; exact hpre j hj⟩, by omega⟩
    · rw [qq 1116 (by omega) (by omega) (by omega) (by omega)]; exact r16
    · rw [qq 1121 (by omega) (by omega) (by omega) (by omega)]; exact r21
    · rw [qq 1112 (by omega) (by omega) (by omega) (by omega)]; exact r12
    · rw [qq 1122 (by omega) (by omega) (by omega) (by omega)]; exact r22
    · rw [qq 1111 (by omega) (by omega) (by omega) (by omega)]; exact r11
    · rw [qq 1110 (by omega) (by omega) (by omega) (by omega)]; exact r10
    · rw [hQ]; exact qx
    · rw [hlab, hQ, h13]; exact core
    · rw [h13]; exact ht
    · rw [hlab, hQ]; exact proc
    · rw [hlab]
      have := core.visit_old hB hs hs1 ht (by rw [qx]; exact part) (by rw [qx]; exact hg1)
        (by rw [qx]; exact hg2) hne
      rwa [qx] at this
    · intro j hj; unfold cwF; rw [mm]; exact hcw j hj
  have b00 : d₁.nreg 0 = 0 := by rw [q₁ 0 (by omega) (by omega) (by omega), e00]
  have b30 : d₁.nreg 1130 = 2 := by rw [q₁ 1130 (by omega) (by omega) (by omega), env.two]
  by_cases h1 : labF c d z = 1
  swap
  · by_cases h0 : labF c d z = 0
    · exact hold h1 d₁ (0 + 2) (.ifLtN_false (by rw [a19, h0, b00]; omega) (.skip hw₁)) rfl
        (by omega)
    · exact hold h1 d₁ (0 + 2 + 1) (.ifLtN_true (by rw [a19, b00]; omega)
        (.ifLtN_false (by rw [a19, b30]; omega) (.skip hw₁))) rfl (by omega)
  -- a new vertex
  have hc1 : d₁.nreg 0 < d₁.nreg 1119 := by rw [a19, h1, b00]; omega
  have hc2 : d₁.nreg 1119 < d₁.nreg 1130 := by rw [a19, h1, b30]; omega
  set t := d.nreg 1113 with htdef
  have htN : t ≤ N := by
    have := core.t_le
    have := card_le_card (cN_subset (G := G) (U := U) (x := s))
    rw [card_UN] at this; omega
  have b13 : d₁.nreg 1113 = t := q₁ 1113 (by omega) (by omega) (by omega)
  have b21 : d₁.nreg 1121 = cc := by rw [q₁ 1121 (by omega) (by omega) (by omega), r21]
  have b03 : d₁.nreg 1103 = c.nreg 1103 := by rw [q₁ 1103 (by omega) (by omega) (by omega), e03]
  obtain ⟨d₂, k₂, e₂, hw₂, n13, q₂, m₂, hk₂⟩ : ∃ d₂ k₂, Exec P W bNew d₁ d₂ k₂ ∧
      WordsBounded W d₂ ∧ d₂.nreg 1113 = t + 1 ∧
      (∀ r, r ≠ 1118 → r ≠ 1113 → d₂.nreg r = d₁.nreg r) ∧
      d₂.nmem = upd (upd d.nmem (c.nreg 1102 + z) cc) (c.nreg 1103 + t) z ∧ k₂ = 4 := by
    unfold bNew
    exec_block
    · config_simp; rw [b03, b13]; omega
    · config_simp; rw [b13, b01]; omega
    · refine ⟨‹WordsBounded _ _›, ?_⟩
      config_simp
      rw [b13, b01, b03, a18, b21, a17, m₁]
      refine ⟨rfl, fun r h1 h2 => ?_, rfl⟩
      simp [h1, h2]
  obtain ⟨d₃, e₃, h15, q₃, m₃, hw₃⟩ := hlast d₂ hw₂
    (by rw [q₂ 1115 (by omega) (by omega)]; exact b15)
    (by rw [q₂ 1001 (by omega) (by omega)]; exact b01)
  have qq : ∀ r, r ≠ 1118 → r ≠ 1119 → r ≠ 1117 → r ≠ 1115 → r ≠ 1113 →
      d₃.nreg r = d.nreg r :=
    fun r a b c' e e' => by rw [q₃ r e, q₂ r a e', q₁ r a b c']
  have mm : d₃.nmem = upd (upd d.nmem (c.nreg 1102 + z) cc) (c.nreg 1103 + t) z := by
    rw [m₃, m₂]
  have hlz : labF c d₃ z = cc := by
    unfold labF; rw [mm, upd_other _ _ _ (by omega), upd_same]
  have hlo : ∀ y < N, y ≠ z → labF c d₃ y = labF c d y := fun y hy hyz => by
    unfold labF; rw [mm, upd_other _ _ _ (by omega), upd_other _ _ _ (by omega)]
  have hQt : QF c d₃ t = z := by unfold QF; rw [mm, upd_same]
  have hQo : ∀ j < t, QF c d₃ j = QF c d j := fun j hj => by
    unfold QF; rw [mm, upd_other _ _ _ (by omega), upd_other _ _ _ (by omega)]
  obtain ⟨core', proc', part', htlt⟩ := core.visit_new hB hcc proc ht (by rw [qx]; exact part)
    (by rw [qx]; exact hg1) (by rw [qx]; exact hg2) h1 hlz hlo hQt hQo
  have htN' : t < N := by
    have := card_le_card (cN_subset (G := G) (U := U) (x := s))
    rw [card_UN] at this; have := card_le_N U; omega
  have h13 : d₃.nreg 1113 = t + 1 := by rw [q₃ 1113 (by omega), n13]
  have hQh : QF c d₃ h = QF c d h := hQo h ht
  refine ⟨d₃, k₁ + (k₂ + 1 + 1 + 1), .seq e₁ (.seq (.ifLtN_true hc1 (.ifLtN_true hc2 e₂)) e₃),
    ⟨⟨hw₃, fun r hr => by
      rw [qq r (by omega) (by omega) (by omega) (by omega) (by omega)]; exact f r hr,
      by rw [qq 1130 (by omega) (by omega) (by omega) (by omega) (by omega)]; exact env.two,
      fun a ha => ?_⟩, h15, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      fun j hj => by rw [hQo j (by omega)]; exact hpre j hj⟩, by omega⟩
  · have h1' : a ≠ c.nreg 1102 + z := fun e => ha (Or.inl ⟨by omega, by omega⟩)
    have h2' : a ≠ c.nreg 1103 + t := fun e => ha (Or.inr (Or.inl ⟨by omega, by omega⟩))
    rw [mm, upd_other _ _ _ h2', upd_other _ _ _ h1']; exact env.fr a ha
  · rw [qq 1116 (by omega) (by omega) (by omega) (by omega) (by omega)]; exact r16
  · rw [qq 1121 (by omega) (by omega) (by omega) (by omega) (by omega)]; exact r21
  · rw [qq 1112 (by omega) (by omega) (by omega) (by omega) (by omega)]; exact r12
  · rw [qq 1122 (by omega) (by omega) (by omega) (by omega) (by omega)]; exact r22
  · rw [qq 1111 (by omega) (by omega) (by omega) (by omega) (by omega)]; exact r11
  · rw [qq 1110 (by omega) (by omega) (by omega) (by omega) (by omega)]; exact r10
  · rw [hQh]; exact qx
  · rw [h13]; exact core'
  · rw [h13]; omega
  · exact proc'
  · rwa [hQo h ht, qx] at part'
  · intro j hj; unfold cwF
    rw [mm, upd_other _ _ _ (by omega), upd_other _ _ _ (by omega)]; exact hcw j hj


variable (G) in
/-- **The state in the loop of the search** from `s` with the label `cc`, `h` vertices of the
queue done. -/
structure SI (U : Finset (Fin N)) (w : Fin N → ℕ) (W : ℕ) (c : Config) (lab₀ cw₀ : ℕ → ℕ)
    (s cc i nc h : ℕ) (d : Config) : Prop where
  env : Env N W c d
  r21 : d.nreg 1121 = cc
  r12 : d.nreg 1112 = h
  r22 : d.nreg 1122 = ∑ j ∈ range h, SepProg.wI w (QF c d j)
  r11 : d.nreg 1111 = nc + 1
  r10 : d.nreg 1110 = i
  core : BCore G U s cc lab₀ (labF c d) (QF c d) (d.nreg 1113)
  hle : h ≤ d.nreg 1113
  proc : Proc G U cc h (labF c d) (QF c d)
  cw : ∀ j ≤ N, cwF c d j = cw₀ j

variable (G) in
/-- The degree of a vertex, from the offsets. -/
noncomputable def dg (x : ℕ) : ℕ := gofs G (x + 1) - gofs G x

theorem bVert_step {c : Config} (hl : CLay G U w W c) {lab₀ cw₀ : ℕ → ℕ}
    {s cc i nc h : ℕ} (hB : BInv G U w i nc lab₀ cw₀) (hcc : cc = nc + 2)
    (hs : s ∈ UN U) (hs1 : lab₀ s = 1) {d : Config}
    (hI : SI G U w W c lab₀ cw₀ s cc i nc h d) (hh : h < d.nreg 1113) :
    ∃ d' k, Exec P W bVert d d' k ∧ SI G U w W c lab₀ cw₀ s cc i nc (h + 1) d' ∧
      (∀ j ≤ h, QF c d' j = QF c d j) ∧ k ≤ 12 + 15 * dg G (QF c d h) := by
  obtain ⟨env, r21, r12, r22, r11, r10, core, hle, proc, hcw⟩ := hI
  have lU := hl.lU; have lC := hl.lC; have lQ := hl.lQ; have lW := hl.lW; have lS := hl.lS
  have l0 := hl.l0; have l1 := hl.l1; have l2 := hl.l2; have l3 := hl.l3; have l4 := hl.l4
  have l5 := hl.l5; have l6 := hl.l6; have l7 := hl.l7; have l8 := hl.l8
  have f := env.fix
  have e03 : d.nreg 1103 = c.nreg 1103 := f 1103 (by omega)
  have e14 : d.nreg 1014 = c.nreg 1014 := f 1014 (by omega)
  have e10 : d.nreg 1010 = c.nreg 1010 := f 1010 (by omega)
  have e01 : d.nreg 1001 = 1 := (f 1001 (by omega)).trans hl.one
  set x := QF c d h with hxdef
  have hxN : x < N := core.lt_N hh
  have htN : d.nreg 1113 ≤ N := by
    have := core.t_le
    have := card_le_card (cN_subset (G := G) (U := U) (x := s))
    rw [card_UN] at this; have := card_le_N U; omega
  have hNW := hl.NW
  have mQ : d.nmem (c.nreg 1103 + h) = x := rfl
  have mW : d.nmem (c.nreg 1014 + x) = SepProg.wI w x := by
    rw [env.fr _ (by unfold Wz; omega)]; exact hl.wt x hxN
  have mO : d.nmem (c.nreg 1010 + x) = gofs G x := by
    rw [env.fr _ (by unfold Wz; omega)]; exact hl.ofs x (by omega)
  have mO' : d.nmem (c.nreg 1010 + x + 1) = gofs G (x + 1) := by
    rw [env.fr _ (by unfold Wz; omega), Nat.add_assoc]; exact hl.ofs (x + 1) (by omega)
  have hsum : ∑ j ∈ range (h + 1), SepProg.wI w (QF c d j) ≤ ∑ v ∈ U, w v := by
    have := core.sum_le (h := h + 1) (by omega) (SepProg.wI w)
    have h2 := sum_le_sum_of_subset_of_nonneg (cN_subset (G := G) (U := U) (x := s))
      (f := SepProg.wI w) (fun _ _ _ => Nat.zero_le _)
    rw [sum_UN] at h2; omega
  rw [sum_range_succ, ← hxdef] at hsum
  have hsw := hl.sw
  obtain ⟨d₁, k₁, e₁, hw₁, a14, a12, a22, a15, a16, q₁, m₁, hk₁⟩ : ∃ d₁ k₁, Exec P W
      (block [.addN 1118 1103 1112, .loadN 1114 1118, .addN 1112 1112 1001,
        .addN 1118 1014 1114, .loadN 1119 1118, .addN 1122 1122 1119, .addN 1118 1010 1114,
        .loadN 1115 1118, .addN 1118 1118 1001, .loadN 1116 1118]) d d₁ k₁ ∧
      WordsBounded W d₁ ∧ d₁.nreg 1114 = x ∧ d₁.nreg 1112 = h + 1 ∧
      d₁.nreg 1122 = ∑ j ∈ range h, SepProg.wI w (QF c d j) + SepProg.wI w x ∧
      d₁.nreg 1115 = gofs G x ∧ d₁.nreg 1116 = gofs G (x + 1) ∧
      (∀ r, r ≠ 1118 → r ≠ 1114 → r ≠ 1112 → r ≠ 1119 → r ≠ 1122 → r ≠ 1115 → r ≠ 1116 →
        d₁.nreg r = d.nreg r) ∧ d₁.nmem = d.nmem ∧ k₁ = 10 := by
    have hw := env.wb
    exec_block
    · rw [e03, r12]; omega
    · config_simp; rw [r12, e01]; omega
    · config_simp; rw [e03, r12, mQ, e14]; omega
    · config_simp; rw [e03, r12, mQ, e14, mW, r22]; omega
    · config_simp; rw [e03, r12, mQ, e10]; omega
    · config_simp; rw [e03, r12, mQ, e10, e01]; omega
    · refine ⟨‹WordsBounded _ _›, ?_⟩
      config_simp
      rw [e03, r12, mQ, e14, mW, r22, e10, mO, e01, mO']
      refine ⟨rfl, rfl, rfl, rfl, rfl, fun r h1 h2 h3 h4 h5 h6 h7 => ?_⟩
      simp [h1, h2, h3, h4, h5, h6, h7]
  have hlab₁ : labF c d₁ = labF c d := by unfold labF; rw [m₁]
  have hQ₁ : QF c d₁ = QF c d := by unfold QF; rw [m₁]
  have h13 : d₁.nreg 1113 = d.nreg 1113 := q₁ 1113 (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega)
  have hD₁ : DI G U W c lab₀ cw₀ (QF c d) s cc h x i nc
      (∑ j ∈ range h, SepProg.wI w (QF c d j) + SepProg.wI w x) (gofs G x) d₁ := {
    env := ⟨hw₁, fun r hr => by
      rw [q₁ r (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
      exact f r hr, by
      rw [q₁ 1130 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
      exact env.two, fun a ha => by rw [m₁]; exact env.fr a ha⟩
    r15 := a15
    r16 := a16
    r21 := by
      rw [q₁ 1121 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
      exact r21
    r12 := a12
    r22 := a22
    r11 := by
      rw [q₁ 1111 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
      exact r11
    r10 := by
      rw [q₁ 1110 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
      exact r10
    qx := by rw [hQ₁]
    core := by rw [hlab₁, hQ₁, h13]; exact core
    ht := by rw [h13]; exact hh
    proc := by rw [hlab₁, hQ₁]; exact proc
    part := fun g' h1 h2 _ => absurd h2 (by omega)
    cw := fun j hj => by unfold cwF; rw [m₁]; exact hcw j hj
    pre := fun j _ => by rw [hQ₁] }
  obtain ⟨d₂, k₂, e₂, ⟨-, hD₂⟩, hk₂⟩ := Exec.forN (P := P) (W := W) (ri := 1115) (rN := 1116)
    (N := gofs G (x + 1)) (lo := gofs G x) (B := 13) (body := bDart)
    (fun g d' => gofs G x ≤ g ∧ DI G U W c lab₀ cw₀ (QF c d) s cc h x i nc
      (∑ j ∈ range h, SepProg.wI w (QF c d j) + SepProg.wI w x) g d')
    (fun g d' h' => ⟨h'.2.env.wb, h'.2.r15, h'.2.r16⟩)
    (fun g d' h' hg => by
      obtain ⟨d'', k, e, h'', hk⟩ := bDart_step hl hB hcc hs hs1 h'.2 h'.1 hg
      exact ⟨d'', k, e, ⟨by omega, h''⟩, hk⟩)
    (gofs_mono G _ _ (by omega) (by omega)) ⟨le_rfl, hD₁⟩
  have hpre := hD₂.pre
  refine ⟨d₂, k₁ + k₂, .seq e₁ e₂, ⟨hD₂.env, hD₂.r21, hD₂.r12, ?_, hD₂.r11, hD₂.r10, hD₂.core,
    hD₂.ht, ?_, hD₂.cw⟩, hpre, ?_⟩
  · rw [hD₂.r22, sum_range_succ, hpre h le_rfl]
    congr 1
    exact sum_congr rfl fun j hj => by rw [hpre j (by have := mem_range.1 hj; omega)]
  · have := hD₂.part
    rw [← hD₂.qx] at this
    exact hD₂.proc.succ this
  · unfold dg; omega

theorem bSearch_exec {c : Config} (hl : CLay G U w W c) {i nc : ℕ} {d : Config}
    (env : Env N W c d) (hi : i < #U) (r10 : d.nreg 1110 = i) (r11 : d.nreg 1111 = nc)
    (r14 : d.nreg 1114 = lv U i) (r18 : d.nreg 1118 = c.nreg 1102 + lv U i)
    (hB : BInv G U w i nc (labF c d) (cwF c d)) (hs1 : labF c d (lv U i) = 1) :
    ∃ d' k, Exec P W bSearch d d' k ∧ Env N W c d' ∧ d'.nreg 1110 = i ∧
      d'.nreg 1111 = nc + 1 ∧ BInv G U w (i + 1) (nc + 1) (labF c d') (cwF c d') ∧
      k ≤ 14 * #(cN G U (lv U i)) + 15 * ∑ y ∈ cN G U (lv U i), dg G y + 11 ∧
      ∀ f : ℕ → ℕ, ∑ x ∈ (UN U).filter (fun x => labF c d x = 1), f x =
        ∑ x ∈ (UN U).filter (fun x => labF c d' x = 1), f x + ∑ x ∈ cN G U (lv U i), f x := by
  have lU := hl.lU; have lC := hl.lC; have lQ := hl.lQ; have lW := hl.lW; have lS := hl.lS
  have l0 := hl.l0; have l1 := hl.l1; have l2 := hl.l2; have l3 := hl.l3; have l4 := hl.l4
  have l5 := hl.l5; have l6 := hl.l6; have l7 := hl.l7; have l8 := hl.l8
  have hNW := hl.NW
  have hU := card_le_N U
  have hnc := hB.ncle
  set s := lv U i with hsdef
  have hs : s ∈ UN U := lv_mem_UN U hi
  have hsN : s < N := lt_of_mem_UN hs
  have f := env.fix
  have e03 : d.nreg 1103 = c.nreg 1103 := f 1103 (by omega)
  have e04 : d.nreg 1104 = c.nreg 1104 := f 1104 (by omega)
  have e01 : d.nreg 1001 = 1 := (f 1001 (by omega)).trans hl.one
  -- the start
  obtain ⟨d₁, k₁, e₁, hw₁, a11, a21, a12, a13, a22, q₁, m₁, hk₁⟩ : ∃ d₁ k₁, Exec P W
      (block [.addN 1111 1111 1001, .addN 1121 1111 1001, .storeN 1118 1121, .storeN 1103 1114,
        .constN 1112 0, .copyN 1113 1001, .constN 1122 0]) d d₁ k₁ ∧ WordsBounded W d₁ ∧
      d₁.nreg 1111 = nc + 1 ∧ d₁.nreg 1121 = nc + 2 ∧ d₁.nreg 1112 = 0 ∧ d₁.nreg 1113 = 1 ∧
      d₁.nreg 1122 = 0 ∧
      (∀ r, r ≠ 1111 → r ≠ 1121 → r ≠ 1112 → r ≠ 1113 → r ≠ 1122 → d₁.nreg r = d.nreg r) ∧
      d₁.nmem = upd (upd d.nmem (c.nreg 1102 + s) (nc + 2)) (c.nreg 1103) s ∧ k₁ = 7 := by
    have hw := env.wb
    exec_block
    · rw [r11, e01]; omega
    · config_simp; rw [r11, e01]; omega
    · omega
    · omega
    · refine ⟨‹WordsBounded _ _›, ?_⟩
      config_simp
      rw [r11, e01, r18, e03, r14]
      refine ⟨rfl, rfl, rfl, fun r h1 h2 h3 h4 h5 => ?_, rfl⟩
      simp [h1, h2, h3, h4, h5]
  have hlab₁ : labF c d₁ (lv U i) = nc + 2 := by
    unfold labF; rw [m₁, upd_other _ _ _ (by omega), upd_same]
  have hlo₁ : ∀ y < N, y ≠ s → labF c d₁ y = labF c d y := fun y hy hys => by
    unfold labF; rw [m₁, upd_other _ _ _ (by omega), upd_other _ _ _ (by omega)]
  have hQ₁ : QF c d₁ 0 = s := by unfold QF; rw [m₁]; simp
  have hcw₁ : ∀ j ≤ N, cwF c d₁ j = cwF c d j := fun j hj => by
    unfold cwF; rw [m₁, upd_other _ _ _ (by omega), upd_other _ _ _ (by omega)]
  have qq₁ : ∀ r < 1110, d₁.nreg r = d.nreg r := fun r hr =>
    q₁ r (by omega) (by omega) (by omega) (by omega) (by omega)
  have env₁ : Env N W c d₁ := ⟨hw₁, fun r hr => by rw [qq₁ r hr]; exact f r hr,
    by rw [q₁ 1130 (by omega) (by omega) (by omega) (by omega) (by omega)]; exact env.two,
    fun a ha => by
      have h1' : a ≠ c.nreg 1102 + s := fun e => ha (Or.inl ⟨by omega, by omega⟩)
      have h2' : a ≠ c.nreg 1103 := fun e => ha (Or.inr (Or.inl ⟨by omega, by omega⟩))
      rw [m₁, upd_other _ _ _ h2', upd_other _ _ _ h1']; exact env.fr a ha⟩
  have hS₁ : SI G U w W c (labF c d) (cwF c d) s (nc + 2) i nc 0 d₁ :=
    ⟨env₁, a21, a12, by rw [a22]; rfl,
      a11,
      by rw [q₁ 1110 (by omega) (by omega) (by omega) (by omega) (by omega)]; exact r10,
      by rw [a13]; exact BCore.start hs hlab₁ hlo₁ hs1 hQ₁ (fun x hx => hB.ne_c hx),
      by rw [a13]; omega, fun j hj => absurd hj (Nat.not_lt_zero _), hcw₁⟩
  -- the loop
  set D := ∑ y ∈ cN G U s, dg G y
  set K := #(cN G U s)
  obtain ⟨d₂, k₂, e₂, ⟨h, hS₂⟩, hn₂, hk₂⟩ := Exec.whileLtN_potential (P := P) (W := W) (a := 1112)
    (b := 1113) (body := bVert)
    (fun d' => ∃ h, SI G U w W c (labF c d) (cwF c d) s (nc + 2) i nc h d')
    (fun d' => 14 * (K - d'.nreg 1112) +
      15 * (D - ∑ j ∈ range (d'.nreg 1112), dg G (QF c d' j)))
    (fun d' ⟨_, h'⟩ => h'.env.wb)
    (fun d' ⟨h, h'⟩ hlt => by
      rw [h'.r12] at hlt
      obtain ⟨d'', k, e, h'', hpre, hk⟩ := bVert_step hl hB rfl hs hs1 h' hlt
      refine ⟨d'', k, e, ⟨h + 1, h''⟩, ?_⟩
      rw [h''.r12, h'.r12, sum_range_succ]
      have hsum : ∑ j ∈ range h, dg G (QF c d'' j) = ∑ j ∈ range h, dg G (QF c d' j) :=
        sum_congr rfl fun j hj => by rw [hpre j (by have := mem_range.1 hj; omega)]
      rw [hsum, hpre h le_rfl]
      have h1 := h''.core.t_le
      have h2 := h''.hle
      have h3 := h''.core.sum_le h''.hle (dg G)
      rw [sum_range_succ, hsum, hpre h le_rfl] at h3
      omega) ⟨0, hS₁⟩
  have hht : h = d₂.nreg 1113 := by have := hS₂.hle; rw [hS₂.r12] at hn₂; omega
  -- the end
  have f₂ := hS₂.env.fix
  have hcw2 : nc + 1 ≤ N := by omega
  obtain ⟨d₃, k₃, e₃, hw₃, q₃, m₃, hk₃⟩ : ∃ d₃ k₃, Exec P W
      (block [.addN 1118 1104 1111, .storeN 1118 1122]) d₂ d₃ k₃ ∧ WordsBounded W d₃ ∧
      (∀ r, r ≠ 1118 → d₃.nreg r = d₂.nreg r) ∧
      d₃.nmem = upd d₂.nmem (c.nreg 1104 + (nc + 1))
        (∑ j ∈ range h, SepProg.wI w (QF c d₂ j)) ∧ k₃ = 2 := by
    have hw := hS₂.env.wb
    exec_block
    · rw [f₂ 1104 (by omega), hS₂.r11]; omega
    · refine ⟨‹WordsBounded _ _›, ?_⟩
      config_simp
      rw [f₂ 1104 (by omega), hS₂.r11, hS₂.r22]
      refine ⟨fun r h1 => by simp [h1], rfl⟩
  have hlab₃ : ∀ x < N, labF c d₃ x = labF c d₂ x := fun x hx => by
    unfold labF; rw [m₃, upd_other _ _ _ (by omega)]
  have hcw₃ : ∀ j, cwF c d₃ j = if j = nc + 1 then ∑ j ∈ range h, SepProg.wI w (QF c d₂ j)
      else cwF c d j := fun j => by
    unfold cwF
    rw [m₃]
    by_cases hj : j = nc + 1
    · rw [hj, upd_same, iteT rfl]
    · rw [upd_other _ _ _ (by omega), iteF hj]
      by_cases hjN : j ≤ N
      · exact hS₂.cw j hjN
      · rw [hS₂.env.fr _ (by unfold Wz; omega), env.fr _ (by unfold Wz; omega)]
  have hP : Proc G U (nc + 2) (d₂.nreg 1113) (labF c d₂) (QF c d₂) := hht ▸ hS₂.proc
  have hB₃ := (BCore.finish hB rfl hi rfl hS₂.core hP
    (cw' := fun j => if j = nc + 1 then ∑ j ∈ range h, SepProg.wI w (QF c d₂ j) else cwF c d j)
    (by rw [iteT rfl, hht]) (fun j hj => by rw [iteF hj])).congr hlab₃ hcw₃
  have hsum := BCore.sum_one hB rfl hs hs1 hS₂.core hP
  refine ⟨d₃, k₁ + (k₂ + k₃), .seq e₁ (.seq e₂ e₃), ⟨hw₃, fun r hr => by
    rw [q₃ r (by omega)]; exact f₂ r hr, by rw [q₃ 1130 (by omega)]; exact hS₂.env.two,
    fun a ha => by
      rw [m₃, upd_other _ _ _ (fun e => ha (Or.inr (Or.inr ⟨by omega, by omega⟩)))]
      exact hS₂.env.fr a ha⟩, by rw [q₃ 1110 (by omega)]; exact hS₂.r10,
    by rw [q₃ 1111 (by omega)]; exact hS₂.r11, hB₃, ?_, fun g => ?_⟩
  · simp only [a12, range_zero, sum_empty, Nat.sub_zero] at hk₂
    omega
  · rw [hsum g]
    congr 1
    refine sum_congr ?_ fun _ _ => rfl
    ext x
    simp only [mem_filter]
    constructor
    · rintro ⟨hx, e⟩; exact ⟨hx, by rw [hlab₃ x (lt_of_mem_UN hx)]; exact e⟩
    · rintro ⟨hx, e⟩; exact ⟨hx, by rw [← hlab₃ x (lt_of_mem_UN hx)]; exact e⟩

variable (G) in
/-- **The potential of the loop over the list**. -/
noncomputable def phiB (U : Finset (Fin N)) (c d : Config) : ℕ :=
  9 * (#U - d.nreg 1110) + 40 * #((UN U).filter fun x => labF c d x = 1) +
    15 * ∑ x ∈ (UN U).filter (fun x => labF c d x = 1), dg G x

theorem bOuter_step {c : Config} (hl : CLay G U w W c) {i nc : ℕ} {d : Config}
    (env : Env N W c d) (hi : i < #U) (r10 : d.nreg 1110 = i) (r11 : d.nreg 1111 = nc)
    (hB : BInv G U w i nc (labF c d) (cwF c d)) :
    ∃ d' k, Exec P W bOuter d d' k ∧ Env N W c d' ∧ d'.nreg 1110 = i + 1 ∧
      (∃ nc', d'.nreg 1111 = nc' ∧ BInv G U w (i + 1) nc' (labF c d') (cwF c d')) ∧
      phiB G U c d' + k + 2 ≤ phiB G U c d := by
  have lU := hl.lU; have lC := hl.lC; have lQ := hl.lQ; have lW := hl.lW; have lS := hl.lS
  have l0 := hl.l0; have l1 := hl.l1; have l2 := hl.l2; have l3 := hl.l3; have l4 := hl.l4
  have l5 := hl.l5; have l6 := hl.l6; have l7 := hl.l7; have l8 := hl.l8
  have hNW := hl.NW
  have hU := card_le_N U
  have f := env.fix
  have e00 : d.nreg 1100 = c.nreg 1100 := f 1100 (by omega)
  have e02 : d.nreg 1102 = c.nreg 1102 := f 1102 (by omega)
  have e01 : d.nreg 1001 = 1 := (f 1001 (by omega)).trans hl.one
  have e01' : d.nreg 1101 = #U := (f 1101 (by omega)).trans hl.uu
  have hsU := lv_mem_UN U hi
  have hsN := lt_of_mem_UN hsU
  have mU : d.nmem (c.nreg 1100 + i) = lv U i := by
    rw [env.fr _ (by unfold Wz; omega)]; exact hl.ul i hi
  obtain ⟨d₁, k₁, e₁, hw₁, a14, a18, a19, q₁, m₁, hk₁⟩ : ∃ d₁ k₁, Exec P W
      (block [.addN 1118 1100 1110, .loadN 1114 1118, .addN 1118 1102 1114, .loadN 1119 1118])
      d d₁ k₁ ∧ WordsBounded W d₁ ∧ d₁.nreg 1114 = lv U i ∧
      d₁.nreg 1118 = c.nreg 1102 + lv U i ∧ d₁.nreg 1119 = labF c d (lv U i) ∧
      (∀ r, r ≠ 1118 → r ≠ 1114 → r ≠ 1119 → d₁.nreg r = d.nreg r) ∧ d₁.nmem = d.nmem ∧
      k₁ = 4 := by
    have hw := env.wb
    exec_block
    · rw [e00, r10]; omega
    · config_simp; rw [e00, r10, mU, e02]; omega
    · refine ⟨‹WordsBounded _ _›, ?_⟩
      config_simp
      rw [e00, r10, mU, e02]
      exact ⟨rfl, rfl, rfl, fun r h1 h2 h3 => by simp [h1, h2, h3]⟩
  have hlab₁ : labF c d₁ = labF c d := by funext x; unfold labF; rw [m₁]
  have hcw₁ : cwF c d₁ = cwF c d := by funext x; unfold cwF; rw [m₁]
  have env₁ : Env N W c d₁ := ⟨hw₁, fun r hr => by
    rw [q₁ r (by omega) (by omega) (by omega)]; exact f r hr,
    by rw [q₁ 1130 (by omega) (by omega) (by omega)]; exact env.two,
    fun a ha => by rw [m₁]; exact env.fr a ha⟩
  have b10 : d₁.nreg 1110 = i := by rw [q₁ 1110 (by omega) (by omega) (by omega), r10]
  have b11 : d₁.nreg 1111 = nc := by rw [q₁ 1111 (by omega) (by omega) (by omega), r11]
  have b30 : d₁.nreg 1130 = 2 := env₁.two
  -- the last instruction
  have hlast : ∀ d₂ : Config, Env N W c d₂ → d₂.nreg 1110 = i →
      ∃ d₃, Exec P W (.instr (.addN 1110 1110 1001)) d₂ d₃ 1 ∧ Env N W c d₃ ∧
        d₃.nreg 1110 = i + 1 ∧ (∀ r, r ≠ 1110 → d₃.nreg r = d₂.nreg r) ∧ d₃.nmem = d₂.nmem := by
    intro d₂ env₂ h10
    have h01 : d₂.nreg 1001 = 1 := (env₂.fix 1001 (by omega)).trans hl.one
    have e := Exec.addN (P := P) env₂.wb 1110 1110 1001 (by rw [h10, h01]; omega)
    refine ⟨_, e, ⟨e.wb_right, fun r hr => ?_, by simp; exact env₂.two, fun a ha => ?_⟩,
      by simp [h10, h01], fun r hr => by simp [hr], rfl⟩
    · simp [show r ≠ 1110 by omega]; exact env₂.fix r hr
    · exact env₂.fr a ha
  by_cases h1 : labF c d (lv U i) < 2
  · have hs1 : labF c d (lv U i) = 1 := by
      by_contra hne
      have := (hB.rng _ hsU hne).1; omega
    obtain ⟨d₂, k₂, e₂, env₂, h10, h11, hB₂, hk₂, hsum₂⟩ := bSearch_exec (P := P) hl env₁ hi b10 b11
      a14 a18 (by rw [hlab₁, hcw₁]; exact hB) (by rw [hlab₁]; exact hs1)
    obtain ⟨d₃, e₃, env₃, h10', q₃, m₃⟩ := hlast d₂ env₂ h10
    have hlab₃ : labF c d₃ = labF c d₂ := by funext x; unfold labF; rw [m₃]
    have hcw₃ : cwF c d₃ = cwF c d₂ := by funext x; unfold cwF; rw [m₃]
    refine ⟨d₃, k₁ + (k₂ + 1 + 1), .seq e₁ (.seq (.ifLtN_true (by rw [a19, b30]; exact h1) e₂)
      e₃), env₃, h10', ⟨nc + 1, by rw [q₃ 1111 (by omega)]; exact h11, by
        rw [hlab₃, hcw₃]; exact hB₂⟩, ?_⟩
    have s1 := hsum₂ (fun _ => 1)
    have s2 := hsum₂ (dg G)
    rw [hlab₁] at s1 s2
    simp only [sum_const, smul_eq_mul, mul_one] at s1
    have hK : 1 ≤ #(cN G U (lv U i)) := card_pos.2 ⟨_, self_mem_cN hsU⟩
    unfold phiB
    rw [hlab₃, h10', r10]
    omega
  · have hne : labF c d (lv U i) ≠ 1 := by omega
    obtain ⟨d₃, e₃, env₃, h10', q₃, m₃⟩ := hlast d₁ env₁ b10
    have hlab₃ : labF c d₃ = labF c d := by funext x; unfold labF; rw [m₃, m₁]
    have hcw₃ : cwF c d₃ = cwF c d := by funext x; unfold cwF; rw [m₃, m₁]
    refine ⟨d₃, k₁ + (0 + 2 + 1), .seq e₁ (.seq (.ifLtN_false (by rw [a19, b30]; exact h1)
      (.skip hw₁)) e₃), env₃, h10', ⟨nc, by rw [q₃ 1111 (by omega)]; exact b11, by
        rw [hlab₃, hcw₃]; exact hB.skip hi hne⟩, ?_⟩
    unfold phiB
    rw [hlab₃, h10', r10]
    omega

theorem compsB_exec {c : Config} (hl : CLay G U w W c) {d : Config} (env : Env N W c d)
    (hlab : ∀ x < N, labF c d x = if x ∈ UN U then 1 else 0)
    (hcw : ∀ j ≤ N, cwF c d j = 0) :
    ∃ d' k, Exec P W compsB d d' k ∧ Env N W c d' ∧
      (∃ nc, BInv G U w #U nc (labF c d') (cwF c d')) ∧
      k ≤ 49 * #U + 15 * ∑ x ∈ UN U, dg G x + 4 := by
  have hNW := hl.NW
  have hU := card_le_N U
  obtain ⟨d₀, k₀, e₀, hw₀, a10, a11, q₀, m₀, hk₀⟩ : ∃ d₀ k₀, Exec P W
      (block [.constN 1110 0, .constN 1111 0]) d d₀ k₀ ∧ WordsBounded W d₀ ∧
      d₀.nreg 1110 = 0 ∧ d₀.nreg 1111 = 0 ∧ (∀ r, r ≠ 1110 → r ≠ 1111 → d₀.nreg r = d.nreg r) ∧
      d₀.nmem = d.nmem ∧ k₀ = 2 := by
    have hw := env.wb
    exec_block
    · omega
    · omega
    · refine ⟨‹WordsBounded _ _›, ?_⟩
      config_simp
      exact fun r h1 h2 => by simp [h1, h2]
  have env₀ : Env N W c d₀ := ⟨hw₀, fun r hr => by rw [q₀ r (by omega) (by omega)]; exact env.fix r hr,
    by rw [q₀ 1130 (by omega) (by omega)]; exact env.two, fun a ha => by rw [m₀]; exact env.fr a ha⟩
  have hB₀ : BInv G U w 0 0 (labF c d₀) (cwF c d₀) := by
    refine BInv.init U w (fun x hx => ?_) (fun x hx hxU => ?_) (fun j hj => ?_)
    · unfold labF; rw [m₀]; have := hlab x (lt_of_mem_UN hx); unfold labF at this
      rw [this, iteT hx]
    · unfold labF; rw [m₀]; have := hlab x hx; unfold labF at this; rw [this, iteF hxU]
    · unfold cwF; rw [m₀]; exact hcw j hj
  have e01' : ∀ d' : Config, Env N W c d' → d'.nreg 1101 = #U := fun d' h =>
    (h.fix 1101 (by omega)).trans hl.uu
  obtain ⟨d₁, k₁, e₁, ⟨env₁, i, hiU, h10, nc, h11, hB₁⟩, hn₁, hk₁⟩ :=
    Exec.whileLtN_potential (P := P) (W := W) (a := 1110) (b := 1101) (body := bOuter)
    (fun d' => Env N W c d' ∧ ∃ i ≤ #U, d'.nreg 1110 = i ∧ ∃ nc, d'.nreg 1111 = nc ∧
      BInv G U w i nc (labF c d') (cwF c d'))
    (phiB G U c) (fun d' h => h.1.wb)
    (fun d' ⟨env', i, hi, h10, nc, h11, hB⟩ hlt => by
      rw [h10, e01' d' env'] at hlt
      obtain ⟨d'', k, e, env'', h10', hB'', hk⟩ := bOuter_step (P := P) hl env' hlt h10 h11 hB
      exact ⟨d'', k, e, ⟨env'', i + 1, hlt, h10', hB''⟩, hk⟩)
    ⟨env₀, 0, Nat.zero_le _, a10, 0, a11, hB₀⟩
  have hi : i = #U := by rw [h10, e01' d₁ env₁] at hn₁; omega
  subst hi
  refine ⟨d₁, k₀ + k₁, .seq e₀ e₁, env₁, ⟨nc, hB₁⟩, ?_⟩
  have hf : (UN U).filter (fun x => labF c d₀ x = 1) = UN U := by
    ext x; simp only [mem_filter, and_iff_left_iff_imp]
    intro hx; unfold labF; rw [m₀]; have := hlab x (lt_of_mem_UN hx); unfold labF at this
    rw [this, iteT hx]
  unfold phiB at hk₁
  rw [hf, a10, card_UN] at hk₁
  omega

theorem compsB_wr : compsB.wr 1120 = false := by decide

end Piece

end PlanarSeparator
