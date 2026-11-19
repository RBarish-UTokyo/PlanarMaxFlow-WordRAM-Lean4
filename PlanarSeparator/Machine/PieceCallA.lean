module

public import PlanarSeparator.Machine.PieceLoops

/-!
# The program of a piece, first part: labels and ranks

The first passes of the program computing `ltComp` for a piece `C` of a graph `G` on `Fin N`
held in global arrays (`Pre`): the labels of the vertices of `C` (`labA`), a first rank pass
(`rankLoop`, with its offsets and weights written to the scratch cells `[0, 2k + 1)`, cleared
afterwards) computing the number `m'` of inner darts and the weight of `C`, so that the layout
of the input of the separator program (`pP`, `kK`, `bB`, `lenL`) can be fixed.

* `swok`: the registers written by a statement (frames by `decide`).
* `labV`: the labels; `rk_after`: the rank array after a rank pass is `rkA`.
* **`front1_exec`**: the state `S1` (labels `labV`, ranks `rkA`, the zero region kept, `m'` and
  the weight in registers).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarSeparator

namespace Piece

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

/-! ### Written registers -/

/-- Every register written by the instruction satisfies `p`. -/
def iwok (p : ℕ → Bool) : Instr → Bool
  | .inputSize a | .constN a _ | .copyN a _ | .addN a _ _ | .subN a _ _ | .mulN a _ _
  | .divN a _ _ | .modN a _ _ | .loadN a _ | .readIn a _ | .rand a _ => p a
  | _ => true

/-- Every register written by the statement satisfies `p`. -/
def swok (p : ℕ → Bool) : Stmt → Bool
  | .skip => true
  | .instr i => iwok p i
  | .seq s t => swok p s && swok p t
  | .ifLtN _ _ s t | .ifLtR _ _ s t => swok p s && swok p t
  | .whileLtN _ _ s | .whileLtR _ _ s => swok p s

theorem wr_of_swok {p : ℕ → Bool} {r : ℕ} (hr : p r = false) :
    ∀ {s : Stmt}, swok p s = true → s.wr r = false
  | .skip, _ => rfl
  | .instr i, h => by
    cases i <;> simp only [swok, iwok] at h <;> simp only [Stmt.wr, Instr.wr] <;>
      simp only [beq_eq_false_iff_ne] <;> rintro rfl <;> simp_all
  | .seq s t, h => by
    simp only [swok, Bool.and_eq_true] at h
    simp [Stmt.wr, wr_of_swok hr h.1, wr_of_swok hr h.2]
  | .ifLtN _ _ s t, h => by
    simp only [swok, Bool.and_eq_true] at h
    simp [Stmt.wr, wr_of_swok hr h.1, wr_of_swok hr h.2]
  | .ifLtR _ _ s t, h => by
    simp only [swok, Bool.and_eq_true] at h
    simp [Stmt.wr, wr_of_swok hr h.1, wr_of_swok hr h.2]
  | .whileLtN _ _ s, h => wr_of_swok hr (s := s) h
  | .whileLtR _ _ s, h => wr_of_swok hr (s := s) h

/-- The scratch registers `[1030, 1070)`. -/
def scr (r : ℕ) : Bool := 1030 ≤ r && r < 1070

theorem nreg_of_scr {P : Input} {W : ℕ} {s : Stmt} {c c' : Config} {t : ℕ}
    (e : Exec P W s c c' t) (hs : swok scr s = true) {r : ℕ} (hr : r < 1030) :
    c'.nreg r = c.nreg r :=
  Exec.nreg_of_wr e (wr_of_swok (by simp [scr]; omega) hs)

variable {N : ℕ} (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]

/-! ### The labels -/

/-- The label of the pass `labA`: `j + 1` at `lv C j`, `0` elsewhere. -/
noncomputable def labV (C : Finset (Fin N)) (x : ℕ) : ℕ :=
  open Classical in
  if h : ∃ j < (clist (ord N) C).length, lv C j = x then Nat.find h + 1 else 0

theorem lv_inj (C : Finset (Fin N)) {i j : ℕ} (hi : i < (clist (ord N) C).length)
    (hj : j < (clist (ord N) C).length) (h : lv C i = lv C j) : i = j := by
  rcases lt_trichotomy i j with h' | h' | h'
  · have := lv_inc C i j h' hj; omega
  · exact h'
  · have := lv_inc C j i h' hi; omega

theorem labV_lv (C : Finset (Fin N)) {j : ℕ} (hj : j < (clist (ord N) C).length) :
    labV C (lv C j) = j + 1 := by
  classical
  unfold labV
  have h : ∃ i < (clist (ord N) C).length, lv C i = lv C j := ⟨j, hj, rfl⟩
  simp only [h, ↓reduceDIte]
  have hs := Nat.find_spec h
  rw [lv_inj C hs.1 hj hs.2]

theorem labV_zero (C : Finset (Fin N)) {x : ℕ} (hx : ∀ j < (clist (ord N) C).length, lv C j ≠ x) :
    labV C x = 0 := by
  classical
  unfold labV
  have h : ¬ ∃ j < (clist (ord N) C).length, lv C j = x := fun ⟨j, hj, h⟩ => hx j hj h
  simp only [h, ↓reduceDIte]

theorem labV_pos (C : Finset (Fin N)) (x : Fin N) : 0 < labV C x ↔ x ∈ C := by
  rw [mem_iff_lv C x]
  constructor
  · intro h
    by_contra hn
    push Not at hn
    rw [labV_zero C hn] at h
    exact lt_irrefl _ h
  · rintro ⟨j, hj, hx⟩
    rw [← hx, labV_lv C hj]; omega

/-- The marking of the rank pass with the labels `labV`: the head is in `C`. -/
theorem labV_hq (C : Finset (Fin N)) (d : G.Dart) (_h : d.fst ∈ C) :
    0 < labV C (tlG G (rvG G (dartNum G d))) ↔ d.snd ∈ C := by
  rw [rvG_dartNum, tlG_dartNum]
  exact labV_pos C d.snd

/-! ### The rank array after a rank pass -/

theorem block_of_mem (C : Finset (Fin N)) (d : G.Dart) (h : d.fst ∈ C) :
    ∃ j < (clist (ord N) C).length, lv C j = d.fst ∧ gofs G (lv C j) ≤ dartNum G d ∧
      (dartNum G d : ℕ) < gofs G (lv C j + 1) := by
  obtain ⟨j, hj, hx⟩ := (mem_iff_lv C d.fst).1 h
  refine ⟨j, hj, hx, ?_, ?_⟩
  · rw [ofs_le_iff, hx]
  · rw [ofs_lt_iff, hx]; omega

theorem fst_of_block (C : Finset (Fin N)) {j : ℕ} (d : G.Dart)
    (h1 : gofs G (lv C j) ≤ dartNum G d) (h2 : (dartNum G d : ℕ) < gofs G (lv C j + 1)) :
    (d.fst : ℕ) = lv C j := by
  have := (ofs_le_iff G d _).1 h1
  have := (ofs_lt_iff G d _).1 h2
  omega

/-- **The rank array after a rank pass** (`rankLoop_exec`): `rkA`, from a rank array that is
`0` on the darts that are not inner. -/
theorem rk_after (C : Finset (Fin N)) (q : ℕ → Prop) [DecidablePred q]
    (hq : ∀ d : G.Dart, d.fst ∈ C → (q (dartNum G d) ↔ d.snd ∈ C)) (aRk : ℕ) (f f0 : ℕ → ℕ)
    (hw : ∀ j < (clist (ord N) C).length, ∀ g, gofs G (lv C j) ≤ g → g < gofs G (lv C j + 1) →
      q g → f (aRk + g) = cntB q (gofs G) (lv C) j + cntI q (gofs G (lv C j)) g + 1)
    (hkeep : ∀ g < nD G, (∀ j < (clist (ord N) C).length, ∀ g', gofs G (lv C j) ≤ g' →
      g' < gofs G (lv C j + 1) → q g' → g ≠ g') → f (aRk + g) = f0 (aRk + g))
    (h0 : ∀ g < nD G, ¬ innerN G C g → f0 (aRk + g) = 0) :
    ∀ g < nD G, f (aRk + g) = rkA G C g := by
  intro g hg
  obtain ⟨d, rfl⟩ := exists_dart_of_lt G hg
  by_cases hi : d.fst ∈ C ∧ d.snd ∈ C
  · obtain ⟨j, hj, -, h1, h2⟩ := block_of_mem G C d hi.1
    rw [hw j hj _ h1 h2 ((hq d hi.1).2 hi.2), rank_lv G C q hq hj h1 h2, rkA_dartNum]
    simp [hi]
  · rw [hkeep _ hg (fun j hj g' h1 h2 hq' he => by
      subst he
      have hf := fst_of_block G C d h1 h2
      have hfC : d.fst ∈ C := (mem_iff_lv C d.fst).2 ⟨j, hj, hf.symm⟩
      exact hi ⟨hfC, (hq d hfC).1 hq'⟩),
      h0 _ hg (fun h => hi ((innerN_dartNum G C d).1 h)), rkA_dartNum]
    simp only [hi, ↓reduceIte]

/-! ### The layout -/

/-- The output base of the separator program. -/
def pP (k m sw : ℕ) : ℕ := 16 * m + 12 * k + 3 * sw + 23
/-- The cost bound of the separator program. -/
def kK (k m : ℕ) : ℕ := 320 * m + 191 * k + 403
/-- The base of the input words. -/
def bB (k m sw : ℕ) : ℕ := pP k m sw + kK k m + 1
/-- The number of input words. -/
def lenL (k m : ℕ) : ℕ := 2 * k + 3 + 3 * m

/-- The number of inner darts. -/
noncomputable def mI (C : Finset (Fin N)) : ℕ :=
  #(univ.filter fun d : G.Dart => d.fst ∈ C ∧ d.snd ∈ C)

variable (R : Kasteleyn.RotationSystem G) (w : Fin N → ℕ) (C : Finset (Fin N)) (Z W : ℕ)

/-- **The state of the machine before the program of the piece `C`**: the registers `1001`
(`1`), `1016` (`#C`), the bases of the global arrays (offsets `1010`, tails `1011`, reversals
`1012`, rotation `1013`, weights `1014`, the list `1015`, labels `1017`, ranks `1018`, marks
`1019`) in increasing order above the zero region `[0, Z)`, the labels and ranks `0`, the
registers `< 1000` and the real cells used by the separator program `0`, and `Z` large enough
for the input of the separator program. -/
structure Pre (c : Config) : Prop where
  wb : WordsBounded W c
  one : c.nreg 1001 = 1
  kk : c.nreg 1016 = #C
  lZ : Z ≤ c.nreg 1010
  l0 : c.nreg 1010 + N < c.nreg 1011
  l1 : c.nreg 1011 + nD G ≤ c.nreg 1012
  l2 : c.nreg 1012 + nD G ≤ c.nreg 1013
  l3 : c.nreg 1013 + nD G ≤ c.nreg 1014
  l4 : c.nreg 1014 + N ≤ c.nreg 1015
  l5 : c.nreg 1015 + N ≤ c.nreg 1017
  l6 : c.nreg 1017 + N ≤ c.nreg 1018
  l7 : c.nreg 1018 + nD G ≤ c.nreg 1019
  l8 : c.nreg 1019 + N ≤ W
  ofs : ∀ v ≤ N, c.nmem (c.nreg 1010 + v) = gofs G v
  tl : ∀ g < nD G, c.nmem (c.nreg 1011 + g) = tlG G g
  rv : ∀ g < nD G, c.nmem (c.nreg 1012 + g) = rvG G g
  ro : ∀ g < nD G, c.nmem (c.nreg 1013 + g) = roG G R g
  wt : ∀ v < N, c.nmem (c.nreg 1014 + v) = SepProg.wI w v
  L : ∀ j < #C, c.nmem (c.nreg 1015 + j) = lv C j
  lab : ∀ x < N, c.nmem (c.nreg 1017 + x) = 0
  rk : ∀ g < nD G, c.nmem (c.nreg 1018 + g) = 0
  zero : ∀ a < Z, c.nmem a = 0
  zreg : ∀ r < 1000, c.nreg r = 0
  rz : ∀ r, r < 1000 ∨ r = 1060 ∨ r = 1001 → c.rreg r = 0
  rmz : ∀ a < Z, c.rmem a = 0
  big : 2 * bB #C (mI G C) (∑ v ∈ C, w v) ≤ Z

/-- The registers kept by the program of a piece. -/
def Kept (r : ℕ) : Prop := r = 1001 ∨ (1010 ≤ r ∧ r ≤ 1019)

/-- **The state after the first passes**: the labels `labV`, the ranks `rkA`, the zero region
and the rest of the memory as before, `m'` in `1037` and the weight of `C` in `1038`. -/
structure S1 (c d : Config) : Prop where
  wb : WordsBounded W d
  regs : ∀ r, (r < 1000 ∨ Kept r) → d.nreg r = c.nreg r
  m' : d.nreg 1037 = mI G C
  sw : d.nreg 1038 = ∑ v ∈ C, w v
  zero : ∀ a < Z, d.nmem a = 0
  lab : ∀ x < N, d.nmem (c.nreg 1017 + x) = labV C x
  rk : ∀ g < nD G, d.nmem (c.nreg 1018 + g) = rkA G C g
  rest : ∀ a, Z ≤ a → (a < c.nreg 1017 ∨ c.nreg 1017 + N ≤ a) →
    (a < c.nreg 1018 ∨ c.nreg 1018 + nD G ≤ a) → d.nmem a = c.nmem a
  out : d.output = c.output
  rr : d.rreg = c.rreg
  rm : d.rmem = c.rmem

/-! ### The first passes -/

/-- The scratch offsets and weights at `0` and `k + 1`. -/
def setupA : Stmt := block [.constN 1050 0, .addN 1051 1016 1001]

/-- Clearing the scratch cells `[0, 2k + 1)`. -/
def clrA : Stmt :=
  .seq (block [.constN 1030 0, .addN 1031 1051 1016, .constN 1039 0]) (clrLoop 1030 1031 1039 1001)

/-- **The first passes**: labels, a rank pass, clearing. -/
def front1 : Stmt := .seq setupA (.seq labA (.seq rankLoop clrA))

theorem wsum_lv (C : Finset (Fin N)) (w : Fin N → ℕ) :
    wsum (SepProg.wI w) (lv C) (clist (ord N) C).length = ∑ v ∈ C, w v := by
  unfold wsum
  conv_rhs => rw [← map_cemb mem_ord C]
  rw [sum_map, ← Fin.sum_univ_eq_sum_range (fun j => SepProg.wI w (lv C j))]
  refine sum_congr rfl fun i _ => ?_
  rw [lv_eq C i.2]
  simp [SepProg.wI]

theorem gofs_mono : ∀ v v', v ≤ v' → v' ≤ N → gofs G v ≤ gofs G v' := fun v v' h _ =>
  card_le_card fun d hd => by
    simp only [mem_filter, mem_univ, true_and] at hd ⊢; omega

theorem nwfG : SepProg.NWf N (nD G) (gofs G) (tlG G) (rvG G) (roG G R) :=
  (SepProg.enc_sepInput R (fun _ => 0) (dartNum G) (fun d d' h => dartNum_lt G h)).nwf

variable {G R w C Z W}

theorem front1_exec {P : Input} {c : Config} (hp : Pre G R w C Z W c) :
    ∃ d t, Exec P W front1 c d t ∧
      t ≤ 80 * #C + 14 * psum (gofs G) (lv C) #C + 30 ∧ S1 G w C Z W c d := by
  have hk : (clist (ord N) C).length = #C := length_clist_ord C
  set k := #C with hkdef
  set aOfs := c.nreg 1010
  set aTl := c.nreg 1011
  set aRv := c.nreg 1012
  set aRo := c.nreg 1013
  set aW := c.nreg 1014
  set aL := c.nreg 1015
  set aLab := c.nreg 1017
  set aRk := c.nreg 1018
  have hkN : k ≤ N := by have := card_le_univ C; simpa using this
  have hbig := hp.big
  have lZ := hp.lZ; have l0 := hp.l0; have l1 := hp.l1; have l2 := hp.l2; have l3 := hp.l3
  have l4 := hp.l4; have l5 := hp.l5; have l6 := hp.l6; have l7 := hp.l7; have l8 := hp.l8
  have hZW : Z ≤ W := by omega
  unfold bB pP kK at hbig
  have hlvN : ∀ j < k, lv C j < N := fun j hj => lv_lt C (by omega)
  have hlinc : ∀ i j, i < j → j < k → lv C i < lv C j := fun i j h hj => lv_inc C i j h (by omega)
  have hlinj : ∀ i < k, ∀ j < k, lv C i = lv C j → i = j := fun i hi j hj h =>
    lv_inj C (by omega) (by omega) h
  -- setupA
  obtain ⟨c₀, t₀, e₀, hw₀, g50, g51, gr₀, gm₀, ht₀⟩ : ∃ c₀ t₀, Exec P W setupA c c₀ t₀ ∧
      WordsBounded W c₀ ∧ c₀.nreg 1050 = 0 ∧ c₀.nreg 1051 = k + 1 ∧
      (∀ r, r ≠ 1050 → r ≠ 1051 → c₀.nreg r = c.nreg r) ∧ c₀.nmem = c.nmem ∧ t₀ = 2 := by
    have hw := hp.wb
    unfold setupA
    exec_block
    · omega
    · config_simp; rw [hp.kk, hp.one]; omega
    · refine ⟨‹WordsBounded _ _›, ?_⟩
      config_simp
      rw [hp.kk, hp.one]
      refine ⟨rfl, fun r h1 h2 => ?_⟩
      simp only [upd_apply]; split_ifs <;> first | omega | rfl
  -- labA
  obtain ⟨c₁, t₁, e₁, ht₁, hlab₁, hfr₁⟩ := labA_exec (P := P) hw₀ (lv C)
    (by rw [gr₀ _ (by omega) (by omega), hp.one]) (by rw [gr₀ _ (by omega) (by omega), hp.kk])
    (fun j hj => by rw [gm₀, gr₀ _ (by omega) (by omega)]; exact hp.L j hj) hlinj
    (fun i hi j hj => by
      rw [gr₀ _ (by omega) (by omega), gr₀ _ (by omega) (by omega)]
      have := hlvN i hi; omega)
    (by omega) (by rw [gr₀ _ (by omega) (by omega)]; omega)
    (fun j hj => by
      rw [gr₀ _ (by omega) (by omega)]
      have := hlvN j hj; omega)
  rw [gr₀ _ (by omega) (by omega)] at hlab₁ hfr₁
  have q₁ : ∀ r, r < 1030 → c₁.nreg r = c₀.nreg r := fun r hr =>
    nreg_of_scr e₁ (by decide) hr
  -- the memory after `labA`
  have m₁ : ∀ a, (a < aLab ∨ aLab + N ≤ a) → c₁.nmem a = c.nmem a := fun a ha => by
    rw [hfr₁ a (fun j hj => by have := hlvN j hj; omega), gm₀]
  have lab₁ : ∀ x < N, c₁.nmem (aLab + x) = labV C x := fun x hx => by
    by_cases h : ∃ j < k, lv C j = x
    · obtain ⟨j, hj, rfl⟩ := h
      rw [hlab₁ j hj, labV_lv C (by omega)]
    · push Not at h
      rw [hfr₁ _ (fun j hj => by have := h j hj; omega), gm₀, hp.lab x hx,
        labV_zero C (fun j hj => h j (by omega))]
  -- the first rank pass
  have hq : ∀ d : G.Dart, d.fst ∈ C →
      ((fun g => 0 < labV C (tlG G (rvG G g))) (dartNum G d) ↔ d.snd ∈ C) :=
    fun d h => labV_hq G C d h
  have hN := nwfG G R
  have r₁ : ∀ r, r < 1030 → r ≠ 1050 → r ≠ 1051 → c₁.nreg r = c.nreg r := fun r h h1 h2 => by
    rw [q₁ r h, gr₀ r h1 h2]
  obtain ⟨c₂, t₂, e₂, ht₂, h37, h38, -, -, hrk₂, hfr₂⟩ := rankLoop_exec (P := P) e₁.wb_right
    (N := N) (M := nD G) (k := k) (lv C) (gofs G) (tlG G) (rvG G) (SepProg.wI w) (labV C)
    (by rw [r₁ _ (by omega) (by omega) (by omega), hp.one])
    (by rw [r₁ _ (by omega) (by omega) (by omega), hp.kk])
    (fun j hj => by
      rw [r₁ _ (by omega) (by omega) (by omega), m₁ _ (by omega)]
      exact hp.L j hj) hlvN hlinc
    (fun v hv => by
      rw [r₁ _ (by omega) (by omega) (by omega), m₁ _ (by omega)]
      exact hp.ofs v hv) (gofs_mono G) (gofs_le G N)
    (fun v hv => by
      rw [r₁ _ (by omega) (by omega) (by omega), m₁ _ (by omega)]
      exact hp.wt v hv)
    (fun g hg => by
      rw [r₁ _ (by omega) (by omega) (by omega), m₁ _ (by omega)]
      exact ⟨hp.rv g hg, hN.rv_lt g hg⟩)
    (fun g hg => by
      rw [r₁ _ (by omega) (by omega) (by omega), m₁ _ (by omega)]
      exact ⟨hp.tl g hg, hN.tl_lt g hg⟩)
    (fun x hx => by rw [r₁ _ (by omega) (by omega) (by omega)]; exact lab₁ x hx)
    (by rw [Exec.nreg_of_wr e₁ (r := 1050) (by decide), Exec.nreg_of_wr e₁ (r := 1051) (by decide),
          g50, g51]; omega)
    (by rw [Exec.nreg_of_wr e₁ (r := 1051) (by decide), q₁ 1010 (by omega), g51,
          gr₀ 1010 (by omega) (by omega)]
        omega)
    (by rw [r₁ _ (by omega) (by omega) (by omega), r₁ 1011 (by omega) (by omega) (by omega)]
        exact hp.l0)
    (by rw [r₁ _ (by omega) (by omega) (by omega), r₁ 1012 (by omega) (by omega) (by omega)]
        exact hp.l1)
    (by rw [r₁ _ (by omega) (by omega) (by omega), r₁ 1014 (by omega) (by omega) (by omega)]
        omega)
    (by rw [r₁ _ (by omega) (by omega) (by omega), r₁ 1015 (by omega) (by omega) (by omega)]
        exact hp.l4)
    (by rw [r₁ _ (by omega) (by omega) (by omega), r₁ 1017 (by omega) (by omega) (by omega)]
        omega)
    (by rw [r₁ _ (by omega) (by omega) (by omega), r₁ 1018 (by omega) (by omega) (by omega)]
        exact hp.l6)
    (by rw [r₁ _ (by omega) (by omega) (by omega)]; omega)
    (by rw [← hk, wsum_lv C w]; omega)
  rw [r₁ 1018 (by omega) (by omega) (by omega)] at hrk₂
  rw [Exec.nreg_of_wr e₁ (r := 1050) (by decide), Exec.nreg_of_wr e₁ (r := 1051) (by decide),
    g50, g51, r₁ 1018 (by omega) (by omega) (by omega)] at hfr₂
  have q₂ : ∀ r, r < 1030 → c₂.nreg r = c₁.nreg r := fun r hr =>
    nreg_of_scr e₂ (by decide) hr
  have r₂ : ∀ r, r < 1030 → r ≠ 1050 → r ≠ 1051 → c₂.nreg r = c.nreg r := fun r h h1 h2 => by
    rw [q₂ r h, r₁ r h h1 h2]
  -- the memory after the first rank pass
  have m₂ : ∀ a, 2 * k + 1 ≤ a → (a < aRk ∨ aRk + nD G ≤ a) → c₂.nmem a = c₁.nmem a :=
    fun a ha hb => hfr₂ a (fun j hj => ⟨by omega, by omega, fun g h1 h2 _ => by
      have := gofs_le G (lv C j + 1); omega⟩)
  have rk₂ : ∀ g < nD G, c₂.nmem (aRk + g) = rkA G C g := by
    refine rk_after G C _ hq aRk c₂.nmem c₁.nmem (fun j hj g h1 h2 hq' => hrk₂ j (by omega) g h1 h2 hq')
      (fun g hg hne => hfr₂ _ (fun j hj => ⟨by omega,
        by omega,
        fun g' h1 h2 h3 => by have := hne j (by omega) g' h1 h2 h3; omega⟩))
      (fun g hg _ => by
        rw [m₁ _ (by omega)]; exact hp.rk g hg)
  -- clearing
  obtain ⟨c₃', t₃', e₃', hw₃', g30, g31, g39, gr₃', gm₃', ht₃'⟩ : ∃ c₃' t₃', Exec P W
      (block [.constN 1030 0, .addN 1031 1051 1016, .constN 1039 0]) c₂ c₃' t₃' ∧
      WordsBounded W c₃' ∧ c₃'.nreg 1030 = 0 ∧ c₃'.nreg 1031 = 2 * k + 1 ∧
      c₃'.nreg 1039 = 0 ∧ (∀ r, r < 1030 → c₃'.nreg r = c₂.nreg r) ∧ c₃'.nmem = c₂.nmem ∧
      t₃' = 3 := by
    have hw := e₂.wb_right
    have a1 : c₂.nreg 1051 = k + 1 := by
      rw [Exec.nreg_of_wr e₂ (r := 1051) (by decide), Exec.nreg_of_wr e₁ (r := 1051) (by decide), g51]
    have a2 : c₂.nreg 1016 = k := by rw [r₂ _ (by omega) (by omega) (by omega), hp.kk]
    exec_block
    · omega
    · config_simp; rw [a1, a2]; omega
    · omega
    · refine ⟨‹WordsBounded _ _›, ?_⟩
      config_simp
      rw [a1, a2]
      refine ⟨by omega, fun r hr => ?_⟩
      simp only [upd_apply]; split_ifs <;> first | omega | rfl
  obtain ⟨c₃, t₃, e₃, ht₃, hz₃, hfr₃⟩ := clrLoop_exec (P := P) hw₃' (ri := 1030) (rb := 1031)
    (rz := 1039) (one := 1001) (by omega) (by omega) (by omega)
    (by rw [gr₃' _ (by omega), r₂ _ (by omega) (by omega) (by omega), hp.one]) g39 g30 g31
    (by omega) (by omega)
  have q₃ : ∀ r, r < 1030 → c₃.nreg r = c₂.nreg r := fun r hr => by
    rw [nreg_of_scr e₃ (by decide) hr, gr₃' r hr]
  have m₃ : ∀ a, 2 * k + 1 ≤ a → c₃.nmem a = c₂.nmem a := fun a ha => by
    rw [hfr₃ a (by omega), gm₃']
  have hfront : Exec P W front1 c c₃ (t₀ + (t₁ + (t₂ + (t₃' + t₃)))) :=
    .seq e₀ (.seq e₁ (.seq e₂ (.seq e₃' e₃)))
  have hwf : ∀ r, (r < 1000 ∨ Kept r) → c₃.nreg r = c.nreg r := fun r hr => by
    rw [q₃ r (by unfold Kept at hr; omega), r₂ r (by unfold Kept at hr; omega)
      (by unfold Kept at hr; omega) (by unfold Kept at hr; omega)]
  refine ⟨c₃, _, hfront, ?_, ⟨e₃.wb_right, hwf, ?_, ?_, fun a ha => ?_, fun x hx => ?_,
    fun g hg => ?_, fun a ha h1 h2 => ?_, ?_, ?_, ?_⟩⟩
  · have := psum_mono (gofs G) (lv C) (le_refl k)
    omega
  · rw [Exec.nreg_of_wr e₃ (r := 1037) (by decide), Exec.nreg_of_wr e₃' (r := 1037) (by decide),
      h37, ← hk]
    exact cntB_lv_card G C _ hq
  · rw [Exec.nreg_of_wr e₃ (r := 1038) (by decide), Exec.nreg_of_wr e₃' (r := 1038) (by decide),
      h38, ← hk, wsum_lv C w]
  · rcases Nat.lt_or_ge a (2 * k + 1) with h | h
    · exact hz₃ a (Nat.zero_le _) h
    · rw [m₃ a h, m₂ a h (by omega),
        m₁ a (by omega)]
      exact hp.zero a ha
  · have := hp.l4
    rw [m₃ _ (by omega), m₂ _ (by omega) (by omega)]
    exact lab₁ x hx
  · have := hp.l4
    rw [m₃ _ (by omega)]
    exact rk₂ g hg
  · have := hp.lZ
    rw [m₃ _ (by omega), m₂ _ (by omega) h2, m₁ _ h1]
  · exact Exec.output_of_ou hfront (by decide)
  · exact (Exec.real_of_noReal hfront (by decide)).1
  · exact (Exec.real_of_noReal hfront (by decide)).2

end Piece

end PlanarSeparator
