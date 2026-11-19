module

public import PlanarSeparator.Machine.CompProg

/-!
# The separator of the components on the machine: the heavy component

After the components (`PlanarSeparator.Piece.compsB_exec`, labels satisfying `BInv` with all of
`U` scanned):

* `pfx_exec`: the common start of the passes over the list of `U` (the vertex `U[i]` in `1114`,
  its label cell in `1118`, its label in `1119`).
* `heavyP`, **`heavyP_exec`**: the first vertex of the list whose component weighs more than
  `2/3` of `U`; its label minus one in `1123` (`0` if there is none), as
  `PlanarSeparator.heavyC`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarSeparator

namespace Piece

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

variable {N : ℕ} {G : SimpleGraph (Fin N)} [DecidableRel G.Adj] {U : Finset (Fin N)}
  {w : Fin N → ℕ} {W : ℕ} {P : Input}

/-- The common start of the passes over the list: `x = U[i]`, its label cell and label. -/
def pfx : List Instr :=
  [.addN 1118 1100 1110, .loadN 1114 1118, .addN 1118 1102 1114, .loadN 1119 1118]

theorem pfx_exec {d : Config} (hw : WordsBounded W d) {aU aC i v : ℕ} (h00 : d.nreg 1100 = aU)
    (h02 : d.nreg 1102 = aC) (h10 : d.nreg 1110 = i) (hm : d.nmem (aU + i) = v)
    (hW1 : aU + i ≤ W) (hW2 : aC + v ≤ W) :
    ∃ d₁, Exec P W (block pfx) d d₁ 4 ∧ WordsBounded W d₁ ∧ d₁.nreg 1114 = v ∧
      d₁.nreg 1118 = aC + v ∧ d₁.nreg 1119 = d.nmem (aC + v) ∧
      (∀ r, r ≠ 1118 → r ≠ 1114 → r ≠ 1119 → d₁.nreg r = d.nreg r) ∧ d₁.nmem = d.nmem := by
  obtain ⟨d₁, k, e, h, rfl⟩ : ∃ d₁ k, Exec P W (block pfx) d d₁ k ∧ (WordsBounded W d₁ ∧
      d₁.nreg 1114 = v ∧ d₁.nreg 1118 = aC + v ∧ d₁.nreg 1119 = d.nmem (aC + v) ∧
      (∀ r, r ≠ 1118 → r ≠ 1114 → r ≠ 1119 → d₁.nreg r = d.nreg r) ∧ d₁.nmem = d.nmem) ∧
      k = 4 := by
    unfold pfx
    exec_block
    · rw [h00, h10]; exact hW1
    · config_simp; rw [h00, h10, hm, h02]; exact hW2
    · refine ⟨⟨‹WordsBounded _ _›, ?_⟩, rfl⟩
      config_simp
      rw [h00, h10, hm, h02]
      exact ⟨rfl, rfl, rfl, fun r h1 h2 h3 => by simp [h1, h2, h3]⟩
  exact ⟨d₁, e, h⟩

/-! ### The heavy component, mathematically -/

variable (G) in
/-- The component of the `l`-th vertex of `U` weighs more than `2/3` of `U`. -/
def hv (U : Finset (Fin N)) (w : Fin N → ℕ) (l : ℕ) : Prop :=
  2 * ∑ v ∈ U, w v < 3 * ∑ y ∈ cN G U (lv U l), SepProg.wI w y

theorem hv_iff {l : ℕ} (hl : l < (ul U).length) :
    hv G U w l ↔ 2 * ∑ v ∈ U, w v < 3 * ∑ u ∈ comp G U (ul U)[l], w u := by
  unfold hv; rw [lv_ul U hl, sum_cN]

theorem heavyC_none (h : ∀ l < #U, ¬ hv G U w l) : heavyC G (ord N) U w = none := by
  rw [heavyC_eq, List.find?_eq_none]
  intro x hx
  obtain ⟨l, hl, rfl⟩ := List.getElem_of_mem hx
  have := h l (by rw [← ul_length]; exact hl)
  rw [hv_iff hl] at this
  simpa using this

theorem heavyC_some {l : ℕ} (hl : l < #U) (h : hv G U w l) (hmin : ∀ l' < l, ¬ hv G U w l') :
    heavyC G (ord N) U w = some ((ul U)[l]'(by rw [ul_length]; exact hl)) := by
  have hl' : l < (ul U).length := by rw [ul_length]; exact hl
  rw [heavyC_eq, List.find?_eq_some_iff_getElem]
  refine ⟨by simpa [hv_iff hl'] using h, l, hl', rfl, fun j hj => ?_⟩
  have := hmin j hj
  rw [hv_iff (by omega)] at this
  simpa using this

/-! ### The program -/

/-- The test of the `i`-th vertex, while no heavy component is found. -/
def heavyTest : Stmt :=
  .seq (block pfx) (.seq (block [.subN 1119 1119 1001, .addN 1118 1104 1119, .loadN 1125 1118,
    .addN 1126 1125 1125, .addN 1126 1126 1125]) (.ifLtN 1124 1126 (.instr (.copyN 1123 1119)) .skip))

/-- **The heavy component**: `1123` is the label minus one of the first heavy component. -/
def heavyP : Stmt :=
  .seq (block [.constN 1123 0, .addN 1124 1120 1120, .constN 1110 0])
    (.whileLtN 1110 1101 (.seq (.ifLtN 1123 1001 heavyTest .skip) (.instr (.addN 1110 1110 1001))))

theorem heavyP_wr : swok cscr heavyP = true := by decide

variable (G) in
/-- The value of `1123` after the first `i` vertices. -/
def HidOK (U : Finset (Fin N)) (w : Fin N → ℕ) (lab : ℕ → ℕ) (i hid : ℕ) : Prop :=
  (hid = 0 ∧ ∀ l < i, ¬ hv G U w l) ∨
    (∃ l < i, hv G U w l ∧ (∀ l' < l, ¬ hv G U w l') ∧ hid = lab (lv U l) - 1 ∧ 1 ≤ hid)

theorem heavyP_exec {c : Config} (hl : CLay G U w W c) {d : Config} (env : Env N W c d)
    {nc : ℕ} (hB : BInv G U w #U nc (labF c d) (cwF c d))
    (h20 : d.nreg 1120 = ∑ v ∈ U, w v) :
    ∃ d' k, Exec P W heavyP d d' k ∧ Env N W c d' ∧ d'.nmem = d.nmem ∧
      d'.nreg 1120 = ∑ v ∈ U, w v ∧ HidOK G U w (labF c d) #U (d'.nreg 1123) ∧
      k ≤ 15 * #U + 5 := by
  have lU := hl.lU; have lC := hl.lC; have lQ := hl.lQ; have lW := hl.lW; have lS := hl.lS
  have l0 := hl.l0; have l1 := hl.l1; have l2 := hl.l2; have l3 := hl.l3; have l4 := hl.l4
  have l5 := hl.l5; have l6 := hl.l6; have l7 := hl.l7; have l8 := hl.l8
  have hNW := hl.NW
  have hU := card_le_N U
  have hsw := hl.sw
  have hnc := hB.ncle
  have f := env.fix
  set wU := ∑ v ∈ U, w v
  obtain ⟨d₀, k₀, e₀, hw₀, a23, a24, a10, q₀, m₀, hk₀⟩ : ∃ d₀ k₀, Exec P W
      (block [.constN 1123 0, .addN 1124 1120 1120, .constN 1110 0]) d d₀ k₀ ∧
      WordsBounded W d₀ ∧ d₀.nreg 1123 = 0 ∧ d₀.nreg 1124 = wU + wU ∧ d₀.nreg 1110 = 0 ∧
      (∀ r, r ≠ 1123 → r ≠ 1124 → r ≠ 1110 → d₀.nreg r = d.nreg r) ∧ d₀.nmem = d.nmem ∧
      k₀ = 3 := by
    have hw := env.wb
    exec_block
    · omega
    · config_simp; rw [h20]; omega
    · omega
    · refine ⟨‹WordsBounded _ _›, by simp, by simp [h20], by simp,
        fun r h1 h2 h3 => by simp [h1, h2, h3], rfl, rfl⟩
  let I : ℕ → Config → Prop := fun i d' => WordsBounded W d' ∧ d'.nreg 1110 = i ∧
    d'.nreg 1101 = #U ∧ (∀ r < 1110, d'.nreg r = d.nreg r) ∧ d'.nreg 1120 = wU ∧
    d'.nreg 1124 = wU + wU ∧ d'.nreg 1130 = 2 ∧ d'.nmem = d.nmem ∧
    HidOK G U w (labF c d) i (d'.nreg 1123)
  have q₀' : ∀ r, r ≠ 1123 → r ≠ 1124 → r ≠ 1110 → d₀.nreg r = d.nreg r := q₀
  have b01 : d₀.nreg 1101 = #U := by
    rw [q₀' 1101 (by omega) (by omega) (by omega), f 1101 (by omega)]; exact hl.uu
  have b20 : d₀.nreg 1120 = wU := by rw [q₀' 1120 (by omega) (by omega) (by omega)]; exact h20
  have b30 : d₀.nreg 1130 = 2 := by
    rw [q₀' 1130 (by omega) (by omega) (by omega)]; exact env.two
  have hI₀ : I 0 d₀ := ⟨hw₀, a10, b01, fun r hr => q₀' r (by omega) (by omega) (by omega),
    b20, a24, b30, m₀, Or.inl ⟨a23, fun l hl => absurd hl (Nat.not_lt_zero _)⟩⟩
  obtain ⟨d₁, k₁, e₁, hI₁, hk₁⟩ := Exec.forN (P := P) (W := W) (ri := 1110) (rN := 1101)
    (N := #U) (lo := 0) (B := 13) (body := .seq (.ifLtN 1123 1001 heavyTest .skip)
      (.instr (.addN 1110 1110 1001))) I (fun i d' h => ⟨h.1, h.2.1, h.2.2.1⟩)
    (fun i d' h hi => by
      obtain ⟨hw, h10, h01, hfix, h20', h24, h30, hm, hok⟩ := h
      have g01 : d'.nreg 1001 = 1 := by rw [hfix 1001 (by omega), f 1001 (by omega)]; exact hl.one
      have g00 : d'.nreg 1100 = c.nreg 1100 := by rw [hfix 1100 (by omega), f 1100 (by omega)]
      have g02 : d'.nreg 1102 = c.nreg 1102 := by rw [hfix 1102 (by omega), f 1102 (by omega)]
      have g04 : d'.nreg 1104 = c.nreg 1104 := by rw [hfix 1104 (by omega), f 1104 (by omega)]
      have hxU := lv_mem_UN U hi
      have hxN := lt_of_mem_UN hxU
      have mU : d'.nmem (c.nreg 1100 + i) = lv U i := by
        rw [hm, env.fr _ (by unfold Wz; omega)]; exact hl.ul i hi
      -- the step on the registers 1110
      have hlast : ∀ d₂ : Config, WordsBounded W d₂ → d₂.nreg 1110 = i → d₂.nreg 1001 = 1 →
          ∃ d₃, Exec P W (.instr (.addN 1110 1110 1001)) d₂ d₃ 1 ∧ WordsBounded W d₃ ∧
            d₃.nreg 1110 = i + 1 ∧ (∀ r, r ≠ 1110 → d₃.nreg r = d₂.nreg r) ∧
            d₃.nmem = d₂.nmem := by
        intro d₂ hw₂ h10' h01'
        have e := Exec.addN (P := P) hw₂ 1110 1110 1001 (by rw [h10', h01']; omega)
        exact ⟨_, e, e.wb_right, by simp [h10', h01'], fun r hr => by simp [hr], rfl⟩
      by_cases h0 : d'.nreg 1123 < d'.nreg 1001
      · have hid0 : d'.nreg 1123 = 0 := by omega
        have hfirst : ∀ l < i, ¬ hv G U w l := by
          rcases hok with ⟨-, h'⟩ | ⟨l, -, -, -, -, h'⟩
          · exact h'
          · omega
        obtain ⟨d₂, e₂, hw₂, b14, b18, b19, q₂, m₂⟩ := pfx_exec (P := P) hw g00 g02 h10 mU
          (by omega) (by omega)
        have hlab2 : 2 ≤ labF c d (lv U i) := hB.final hxU
        have hlabN : labF c d (lv U i) ≤ nc + 1 := (hB.rng _ hxU (by omega)).2
        have hwt := hB.wt _ hxU hlab2
        have hle : ∑ y ∈ cN G U (lv U i), SepProg.wI w y ≤ wU := by
          have := sum_le_sum_of_subset_of_nonneg (cN_subset (G := G) (U := U) (x := lv U i))
            (f := SepProg.wI w) (fun _ _ _ => Nat.zero_le _)
          rw [sum_UN] at this; exact this
        have b19' : d₂.nreg 1119 = labF c d (lv U i) := by rw [b19, hm]; rfl
        have mC : d₂.nmem (c.nreg 1104 + (labF c d (lv U i) - 1)) =
            ∑ y ∈ cN G U (lv U i), SepProg.wI w y := by rw [m₂, hm]; exact hwt
        have g04' : d₂.nreg 1104 = c.nreg 1104 := by
          rw [q₂ 1104 (by omega) (by omega) (by omega), g04]
        have g01' : d₂.nreg 1001 = 1 := by rw [q₂ 1001 (by omega) (by omega) (by omega), g01]
        obtain ⟨d₃, k₃, e₃, hw₃, c19, c26, q₃, m₃, hk₃⟩ : ∃ d₃ k₃, Exec P W
            (block [.subN 1119 1119 1001, .addN 1118 1104 1119, .loadN 1125 1118,
              .addN 1126 1125 1125, .addN 1126 1126 1125]) d₂ d₃ k₃ ∧ WordsBounded W d₃ ∧
            d₃.nreg 1119 = labF c d (lv U i) - 1 ∧
            d₃.nreg 1126 = 3 * ∑ y ∈ cN G U (lv U i), SepProg.wI w y ∧
            (∀ r, r ≠ 1119 → r ≠ 1118 → r ≠ 1125 → r ≠ 1126 → d₃.nreg r = d₂.nreg r) ∧
            d₃.nmem = d₂.nmem ∧ k₃ = 5 := by
          exec_block
          · config_simp; rw [g04', b19', g01']; omega
          · config_simp; rw [g04', b19', g01', mC]; omega
          · config_simp; rw [g04', b19', g01', mC]; omega
          · refine ⟨‹WordsBounded _ _›, ?_⟩
            config_simp
            rw [g04', b19', g01', mC]
            exact ⟨rfl, by ring, fun r h1 h2 h3 h4 => by simp [h1, h2, h3, h4]⟩
        have qq : ∀ r, r ≠ 1119 → r ≠ 1118 → r ≠ 1125 → r ≠ 1126 → r ≠ 1114 → r ≠ 1123 →
            ∀ d₄ : Config, (∀ r, r ≠ 1123 → d₄.nreg r = d₃.nreg r) → d₄.nreg r = d'.nreg r :=
          fun r a b c' e g h d₄ h4 => by rw [h4 r h, q₃ r a b c' e, q₂ r b g a]
        by_cases hh : d₃.nreg 1124 < d₃.nreg 1126
        · have e4 := Exec.copyN (P := P) hw₃ 1123 1119
          obtain ⟨d₅, e₅, hw₅, h10'', q₅, m₅⟩ := hlast _ e4.wb_right
            (by simp; rw [q₃ 1110 (by omega) (by omega) (by omega) (by omega),
              q₂ 1110 (by omega) (by omega) (by omega), h10])
            (by simp; rw [q₃ 1001 (by omega) (by omega) (by omega) (by omega), g01'])
          have hhv : hv G U w i := by
            unfold hv
            rw [q₃ 1124 (by omega) (by omega) (by omega) (by omega),
              q₂ 1124 (by omega) (by omega) (by omega), h24, c26] at hh
            omega
          have qq' : ∀ r, r ≠ 1119 → r ≠ 1118 → r ≠ 1125 → r ≠ 1126 → r ≠ 1114 → r ≠ 1110 →
              r ≠ 1123 → d₅.nreg r = d'.nreg r := fun r a b c' e g h k => by
            rw [q₅ r h]; simp only [upd_other _ _ _ k]
            rw [q₃ r a b c' e, q₂ r b g a]
          have c23 : d₅.nreg 1123 = labF c d (lv U i) - 1 := by
            rw [q₅ 1123 (by omega)]; simp only [upd_same]; exact c19
          refine ⟨d₅, _, .seq (.ifLtN_true h0 (.seq e₂ (.seq e₃
            (.ifLtN_true hh e4)))) e₅, ⟨hw₅, h10'', ?_, fun r hr => ?_, ?_, ?_, ?_, ?_, ?_⟩,
            by omega⟩
          · rw [qq' 1101 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
              (by omega)]; exact h01
          · rw [qq' r (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
              (by omega)]; exact hfix r hr
          · rw [qq' 1120 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
              (by omega)]; exact h20'
          · rw [qq' 1124 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
              (by omega)]; exact h24
          · rw [qq' 1130 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
              (by omega)]; exact h30
          · rw [m₅]; rw [m₃, m₂, hm]
          · rw [c23]
            exact Or.inr ⟨i, Nat.lt_succ_self _, hhv, hfirst, rfl, by omega⟩
        · obtain ⟨d₅, e₅, hw₅, h10'', q₅, m₅⟩ := hlast d₃ hw₃
            (by rw [q₃ 1110 (by omega) (by omega) (by omega) (by omega),
              q₂ 1110 (by omega) (by omega) (by omega), h10])
            (by rw [q₃ 1001 (by omega) (by omega) (by omega) (by omega), g01'])
          have hhv : ¬ hv G U w i := by
            unfold hv
            rw [q₃ 1124 (by omega) (by omega) (by omega) (by omega),
              q₂ 1124 (by omega) (by omega) (by omega), h24, c26] at hh
            omega
          have qq' : ∀ r, r ≠ 1119 → r ≠ 1118 → r ≠ 1125 → r ≠ 1126 → r ≠ 1114 → r ≠ 1110 →
              d₅.nreg r = d'.nreg r := fun r a b c' e g h => by
            rw [q₅ r h, q₃ r a b c' e, q₂ r b g a]
          refine ⟨d₅, _, .seq (.ifLtN_true h0 (.seq e₂ (.seq e₃
            (.ifLtN_false hh (.skip hw₃))))) e₅, ⟨hw₅, h10'', ?_, fun r hr => ?_, ?_, ?_, ?_,
            ?_, ?_⟩, by omega⟩
          · rw [qq' 1101 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
            exact h01
          · rw [qq' r (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
            exact hfix r hr
          · rw [qq' 1120 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
            exact h20'
          · rw [qq' 1124 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
            exact h24
          · rw [qq' 1130 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
            exact h30
          · rw [m₅, m₃, m₂, hm]
          rw [qq' 1123 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), hid0]
          refine Or.inl ⟨rfl, fun l hl => ?_⟩
          rcases Nat.lt_succ_iff_lt_or_eq.1 hl with hl | rfl
          · exact hfirst l hl
          · exact hhv
      · obtain ⟨d₅, e₅, hw₅, h10'', q₅, m₅⟩ := hlast d' hw h10 g01
        refine ⟨d₅, 0 + 2 + 1, .seq (.ifLtN_false h0 (.skip hw)) e₅, ⟨hw₅, h10'',
          (by rw [q₅ 1101 (by omega)]; exact h01),
          fun r hr => (by rw [q₅ r (by omega)]; exact hfix r hr),
          (by rw [q₅ 1120 (by omega)]; exact h20'), (by rw [q₅ 1124 (by omega)]; exact h24),
          (by rw [q₅ 1130 (by omega)]; exact h30), (by rw [m₅, hm]), ?_⟩, by omega⟩
        rw [q₅ 1123 (by omega)]
        rcases hok with ⟨h', -⟩ | ⟨l, hl, h1, h2, h3, h4⟩
        · omega
        · exact Or.inr ⟨l, by omega, h1, h2, h3, h4⟩)
    (Nat.zero_le _) hI₀
  obtain ⟨hw₁, -, -, hfix₁, h20₁, -, h30₁, hm₁, hok₁⟩ := hI₁
  refine ⟨d₁, k₀ + k₁, .seq e₀ e₁, ⟨hw₁, fun r hr => by rw [hfix₁ r hr]; exact f r hr, h30₁,
    fun a ha => by rw [hm₁]; exact env.fr a ha⟩, hm₁, h20₁, hok₁, by omega⟩

/-! ### The list of the heavy component -/

theorem filter_ul {C : Finset (Fin N)} (hCU : C ⊆ U) : (ul U).filter (· ∈ C) = ul C := by
  rw [show ul U = (ord N).filter (· ∈ U) from clist_eq U,
    show ul C = (ord N).filter (· ∈ C) from clist_eq C, List.filter_filter]
  congr 1
  funext v
  by_cases h : v ∈ C
  · simp [h, hCU h]
  · simp [h]

theorem take_succ_ul {i : ℕ} (hi : i < (ul U).length) :
    (ul U).take (i + 1) = (ul U).take i ++ [(ul U)[i]] := by
  rw [List.take_add_one, List.getElem?_eq_getElem hi]; rfl

/-- The vertices of `C` among the first `i` vertices of the list of `U`. -/
def Lc (U C : Finset (Fin N)) (i : ℕ) : List ℕ :=
  (((ul U).take i).filter (· ∈ C)).map Fin.val

theorem Lc_succ (U C : Finset (Fin N)) {i : ℕ} (hi : i < #U) :
    Lc U C (i + 1) = Lc U C i ++ if (⟨lv U i, lv_ltN U hi⟩ : Fin N) ∈ C then [lv U i] else [] := by
  have hi' : i < (ul U).length := by rw [ul_length]; exact hi
  have hv : (⟨lv U i, lv_ltN U hi⟩ : Fin N) = (ul U)[i] := Fin.ext (lv_ul U hi')
  unfold Lc
  rw [take_succ_ul hi', List.filter_append, List.map_append, hv]
  by_cases h : (ul U)[i] ∈ C
  · simp [h, lv_ul U hi']
  · simp [h]

theorem Lc_len_le (U C : Finset (Fin N)) (i : ℕ) : (Lc U C i).length ≤ i := by
  unfold Lc
  rw [List.length_map]
  exact (List.length_filter_le _ _).trans (List.length_take_le _ _)

theorem Lc_all {C : Finset (Fin N)} (hCU : C ⊆ U) : Lc U C #U = (ul C).map Fin.val := by
  unfold Lc
  rw [← ul_length, List.take_length, filter_ul hCU]

/-- **The list of a component**: the vertices of the list of `U` with the label `1121`, written
to `aL` (register `1015`), their number in `1127`. -/
def lBody : Stmt :=
  .seq (block pfx) (.seq (.ifLtN 1119 1121 .skip (.ifLtN 1121 1119 .skip
    (block [.addN 1118 1015 1127, .storeN 1118 1114, .addN 1127 1127 1001])))
    (.instr (.addN 1110 1110 1001)))

/-- The pass writing the list. -/
def lPass : Stmt :=
  .seq (block [.constN 1110 0, .constN 1127 0]) (.whileLtN 1110 1101 lBody)

theorem lPass_exec {c : Config} (hl : CLay G U w W c) {d : Config} (env : Env N W c d)
    {C : Finset (Fin N)} {hb : ℕ} (hCU : C ⊆ U) (h21 : d.nreg 1121 = hb)
    (hC : ∀ x (hx : x ∈ UN U), (⟨x, lt_of_mem_UN hx⟩ : Fin N) ∈ C ↔ labF c d x = hb) :
    ∃ d' k, Exec P W lPass d d' k ∧ WordsBounded W d' ∧
      (∀ r, r < 1110 ∨ r = 1120 ∨ r = 1121 ∨ r = 1123 ∨ r = 1130 → d'.nreg r = d.nreg r) ∧
      d'.nreg 1127 = #C ∧ (∀ j < #C, d'.nmem (c.nreg 1015 + j) = lv C j) ∧
      (∀ a, a < c.nreg 1015 ∨ c.nreg 1015 + N ≤ a → d'.nmem a = d.nmem a) ∧
      k ≤ 14 * #U + 4 := by
  have lU := hl.lU; have lC := hl.lC; have lQ := hl.lQ; have lW := hl.lW; have lS := hl.lS
  have l0 := hl.l0; have l1 := hl.l1; have l2 := hl.l2; have l3 := hl.l3; have l4 := hl.l4
  have l5 := hl.l5; have l6 := hl.l6; have l7 := hl.l7; have l8 := hl.l8
  have hNW := hl.NW
  have hU := card_le_N U
  have f := env.fix
  set aL := c.nreg 1015
  obtain ⟨d₀, k₀, e₀, hw₀, a10, a27, q₀, m₀, hk₀⟩ : ∃ d₀ k₀, Exec P W
      (block [.constN 1110 0, .constN 1127 0]) d d₀ k₀ ∧ WordsBounded W d₀ ∧
      d₀.nreg 1110 = 0 ∧ d₀.nreg 1127 = 0 ∧ (∀ r, r ≠ 1110 → r ≠ 1127 → d₀.nreg r = d.nreg r) ∧
      d₀.nmem = d.nmem ∧ k₀ = 2 := by
    have hw := env.wb
    exec_block
    · omega
    · omega
    · exact ⟨‹WordsBounded _ _›, by simp, by simp, fun r h1 h2 => by simp [h1, h2], rfl, rfl⟩
  let I : ℕ → Config → Prop := fun i d' => WordsBounded W d' ∧ d'.nreg 1110 = i ∧
    d'.nreg 1101 = #U ∧
    (∀ r, r < 1110 ∨ r = 1120 ∨ r = 1121 ∨ r = 1123 ∨ r = 1130 → d'.nreg r = d.nreg r) ∧
    d'.nreg 1127 = (Lc U C i).length ∧
    (∀ j < (Lc U C i).length, d'.nmem (aL + j) = (Lc U C i).getD j 0) ∧
    (∀ a, a < aL ∨ aL + N ≤ a → d'.nmem a = d.nmem a)
  have hI₀ : I 0 d₀ := ⟨hw₀, a10, by
      rw [q₀ 1101 (by omega) (by omega), f 1101 (by omega)]; exact hl.uu,
    fun r hr => q₀ r (by omega) (by omega), by rw [a27]; simp [Lc],
    fun j hj => by simp [Lc] at hj, fun a _ => by rw [m₀]⟩
  obtain ⟨d₁, k₁, e₁, hI₁, hk₁⟩ := Exec.forN (P := P) (W := W) (ri := 1110) (rN := 1101)
    (N := #U) (lo := 0) (B := 12) (body := lBody) I (fun i d' h => ⟨h.1, h.2.1, h.2.2.1⟩)
    (fun i d' h hi => by
      obtain ⟨hw, h10, h01, hfix, h27, hL, hfr⟩ := h
      have g01 : d'.nreg 1001 = 1 := by
        rw [hfix 1001 (Or.inl (by omega)), f 1001 (by omega)]; exact hl.one
      have g00 : d'.nreg 1100 = c.nreg 1100 := by
        rw [hfix 1100 (Or.inl (by omega)), f 1100 (by omega)]
      have g02 : d'.nreg 1102 = c.nreg 1102 := by
        rw [hfix 1102 (Or.inl (by omega)), f 1102 (by omega)]
      have g15 : d'.nreg 1015 = aL := by rw [hfix 1015 (Or.inl (by omega)), f 1015 (by omega)]
      have g21 : d'.nreg 1121 = hb := by rw [hfix 1121 (by omega)]; exact h21
      have hxU := lv_mem_UN U hi
      have hxN := lt_of_mem_UN hxU
      have mU : d'.nmem (c.nreg 1100 + i) = lv U i := by
        rw [hfr _ (Or.inl (by omega)), env.fr _ (by unfold Wz; omega)]; exact hl.ul i hi
      have mlab : d'.nmem (c.nreg 1102 + lv U i) = labF c d (lv U i) := hfr _ (Or.inl (by omega))
      obtain ⟨d₂, e₂, hw₂, b14, b18, b19, q₂, m₂⟩ := pfx_exec (P := P) hw g00 g02 h10 mU
        (by omega) (by omega)
      rw [mlab] at b19
      have hlen := Lc_len_le U C i
      have hlast : ∀ d₃ : Config, WordsBounded W d₃ → d₃.nreg 1110 = i → d₃.nreg 1001 = 1 →
          ∃ d₄, Exec P W (.instr (.addN 1110 1110 1001)) d₃ d₄ 1 ∧ WordsBounded W d₄ ∧
            d₄.nreg 1110 = i + 1 ∧ (∀ r, r ≠ 1110 → d₄.nreg r = d₃.nreg r) ∧
            d₄.nmem = d₃.nmem := by
        intro d₃ hw₃ h10' h01'
        have e := Exec.addN (P := P) hw₃ 1110 1110 1001 (by rw [h10', h01']; omega)
        exact ⟨_, e, e.wb_right, by simp [h10', h01'], fun r hr => by simp [hr], rfl⟩
      have q2' : ∀ r, r ≠ 1118 → r ≠ 1114 → r ≠ 1119 → d₂.nreg r = d'.nreg r := q₂
      by_cases hin : (⟨lv U i, hxN⟩ : Fin N) ∈ C
      · have heq : labF c d (lv U i) = hb := (hC _ hxU).1 hin
        have t1 : ¬ d₂.nreg 1119 < d₂.nreg 1121 := by
          rw [b19, q2' 1121 (by omega) (by omega) (by omega), g21, heq]; omega
        have t2 : ¬ d₂.nreg 1121 < d₂.nreg 1119 := by
          rw [b19, q2' 1121 (by omega) (by omega) (by omega), g21, heq]; omega
        have c27 : d₂.nreg 1127 = (Lc U C i).length := by
          rw [q2' 1127 (by omega) (by omega) (by omega), h27]
        have c15 : d₂.nreg 1015 = aL := by rw [q2' 1015 (by omega) (by omega) (by omega), g15]
        have c01 : d₂.nreg 1001 = 1 := by rw [q2' 1001 (by omega) (by omega) (by omega), g01]
        obtain ⟨d₃, k₃, e₃, hw₃, c27', q₃, m₃, hk₃⟩ : ∃ d₃ k₃, Exec P W
            (block [.addN 1118 1015 1127, .storeN 1118 1114, .addN 1127 1127 1001]) d₂ d₃ k₃ ∧
            WordsBounded W d₃ ∧ d₃.nreg 1127 = (Lc U C i).length + 1 ∧
            (∀ r, r ≠ 1118 → r ≠ 1127 → d₃.nreg r = d₂.nreg r) ∧
            d₃.nmem = upd d₂.nmem (aL + (Lc U C i).length) (lv U i) ∧ k₃ = 3 := by
          exec_block
          · rw [c15, c27]; omega
          · config_simp; rw [c27, c01]; omega
          · refine ⟨‹WordsBounded _ _›, ?_⟩
            config_simp
            rw [c15, c27, c01, b14]
            exact ⟨rfl, fun r h1 h2 => by simp [h1, h2], rfl⟩
        obtain ⟨d₄, e₄, hw₄, h10', q₄, m₄⟩ := hlast d₃ hw₃
          (by rw [q₃ 1110 (by omega) (by omega), q2' 1110 (by omega) (by omega) (by omega), h10])
          (by rw [q₃ 1001 (by omega) (by omega), c01])
        have hLs : Lc U C (i + 1) = Lc U C i ++ [lv U i] := by
          rw [Lc_succ U C hi, iteT hin]
        refine ⟨d₄, _, .seq e₂ (.seq (.ifLtN_false t1 (.ifLtN_false t2 e₃)) e₄),
          ⟨hw₄, h10', ?_, fun r hr => ?_, ?_, fun j hj => ?_, fun a ha => ?_⟩, by omega⟩
        · rw [q₄ 1101 (by omega), q₃ 1101 (by omega) (by omega),
            q2' 1101 (by omega) (by omega) (by omega)]; exact h01
        · rw [q₄ r (by omega), q₃ r (by omega) (by omega), q2' r (by omega) (by omega)
            (by omega)]; exact hfix r hr
        · rw [q₄ 1127 (by omega), c27', hLs, List.length_append]; rfl
        · rw [hLs, List.length_append] at hj
          rw [m₄, m₃, hLs]
          rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
          · rw [upd_other _ _ _ (by omega), m₂, hL j hj, List.getD_append _ _ _ _ hj]
          · rw [upd_same, List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self]; rfl
        · rw [m₄, m₃, upd_other _ _ _ (by omega), m₂, hfr a ha]
      · have hne : labF c d (lv U i) ≠ hb := fun h => hin ((hC _ hxU).2 h)
        have hLs : Lc U C (i + 1) = Lc U C i := by rw [Lc_succ U C hi, iteF hin, List.append_nil]
        have c01 : d₂.nreg 1001 = 1 := by rw [q2' 1001 (by omega) (by omega) (by omega), g01]
        obtain ⟨d₄, e₄, hw₄, h10', q₄, m₄⟩ := hlast d₂ hw₂
          (by rw [q2' 1110 (by omega) (by omega) (by omega), h10]) c01
        have qq : ∀ r, r ≠ 1118 → r ≠ 1114 → r ≠ 1119 → r ≠ 1110 → d₄.nreg r = d'.nreg r :=
          fun r a b c' e => by rw [q₄ r e, q2' r a b c']
        have hI' : I (i + 1) d₄ := ⟨hw₄, h10', by
            rw [qq 1101 (by omega) (by omega) (by omega) (by omega)]; exact h01,
          fun r hr => by rw [qq r (by omega) (by omega) (by omega) (by omega)]; exact hfix r hr,
          by rw [qq 1127 (by omega) (by omega) (by omega) (by omega), hLs]; exact h27,
          fun j hj => by rw [hLs] at hj ⊢; rw [m₄, m₂]; exact hL j hj,
          fun a ha => by rw [m₄, m₂]; exact hfr a ha⟩
        have g21' : d₂.nreg 1121 = hb := by rw [q2' 1121 (by omega) (by omega) (by omega), g21]
        by_cases hlt : labF c d (lv U i) < hb
        · exact ⟨d₄, _, .seq e₂ (.seq (.ifLtN_true (by rw [b19, g21']; exact hlt)
            (.skip hw₂)) e₄), hI', by omega⟩
        · exact ⟨d₄, _, .seq e₂ (.seq (.ifLtN_false (by rw [b19, g21']; exact hlt)
            (.ifLtN_true (by rw [b19, g21']; omega) (.skip hw₂))) e₄), hI', by omega⟩)
    (Nat.zero_le _) hI₀
  obtain ⟨hw₁, -, -, hfix₁, h27₁, hL₁, hfr₁⟩ := hI₁
  have hall := Lc_all hCU
  have hlenC : (Lc U C #U).length = #C := by rw [hall, List.length_map, ul_length]
  refine ⟨d₁, k₀ + k₁, .seq e₀ e₁, hw₁, hfix₁, by rw [h27₁, hlenC], fun j hj => ?_, hfr₁,
    by omega⟩
  rw [hL₁ j (by omega), hall]
  rfl

/-! ### The state for the program of a piece -/

variable (G) in
/-- **The state before the separator of the components**: the layout `CLay`, the rotation, the
labels and ranks of `Pre` zero, the zero region `[0, Z)` below the list of `U`, the registers
below `1000` and the real cells zero, and `Z` large enough for every piece of `U`. -/
structure CPre (R : Kasteleyn.RotationSystem G) (w : Fin N → ℕ) (U : Finset (Fin N)) (Z W : ℕ)
    (c : Config) : Prop where
  lay : CLay G U w W c
  ro : ∀ g < nD G, c.nmem (c.nreg 1013 + g) = roG G R g
  lab : ∀ x < N, c.nmem (c.nreg 1017 + x) = 0
  rk : ∀ g < nD G, c.nmem (c.nreg 1018 + g) = 0
  lZ : Z ≤ c.nreg 1100
  zero : ∀ a < Z, c.nmem a = 0
  zreg : ∀ r < 1000, c.nreg r = 0
  rz : ∀ r, r < 1000 ∨ r = 1060 ∨ r = 1001 → c.rreg r = 0
  rmz : ∀ a < Z, c.rmem a = 0
  big : 2 * bB #U (mI G U) (∑ v ∈ U, w v) ≤ Z

theorem mI_mono {C D : Finset (Fin N)} (h : C ⊆ D) : mI G C ≤ mI G D :=
  card_le_card fun d hd => by
    simp only [mem_filter, mem_univ, true_and] at hd ⊢; exact ⟨h hd.1, h hd.2⟩

theorem bB_mono {k k' m m' s s' : ℕ} (hk : k ≤ k') (hm : m ≤ m') (hs : s ≤ s') :
    bB k m s ≤ bB k' m' s' := by
  unfold bB pP kK; omega

theorem pre_of {R : Kasteleyn.RotationSystem G} {Z : ℕ} {c d : Config}
    (hp : CPre G R w U Z W c) {C : Finset (Fin N)} (hCU : C ⊆ U) (hw : WordsBounded W d)
    (hr : ∀ r < 1110, r ≠ 1016 → d.nreg r = c.nreg r) (h16 : d.nreg 1016 = #C)
    (hm : ∀ a, ¬ Wz (N := N) c a → (a < c.nreg 1015 ∨ c.nreg 1015 + N ≤ a) →
      d.nmem a = c.nmem a)
    (hL : ∀ j < #C, d.nmem (c.nreg 1015 + j) = lv C j) (hrr : d.rreg = c.rreg)
    (hrm : d.rmem = c.rmem) : Pre G R w C Z W d := by
  have hl := hp.lay
  have lU := hl.lU; have lC := hl.lC; have lQ := hl.lQ; have lW := hl.lW; have lS := hl.lS
  have l0 := hl.l0; have l1 := hl.l1; have l2 := hl.l2; have l3 := hl.l3; have l4 := hl.l4
  have l5 := hl.l5; have l6 := hl.l6; have l7 := hl.l7; have l8 := hl.l8
  have hZ := hp.lZ
  have g : ∀ r, 1010 ≤ r → r ≤ 1019 → r ≠ 1016 → d.nreg r = c.nreg r := fun r h1 h2 h3 =>
    hr r (by omega) h3
  have hfar : ∀ a, c.nreg 1010 ≤ a → a < c.nreg 1015 → d.nmem a = c.nmem a := fun a h1 h2 =>
    hm a (by unfold Wz; omega) (Or.inl h2)
  have hfar' : ∀ a, c.nreg 1015 + N ≤ a → d.nmem a = c.nmem a := fun a h1 =>
    hm a (by unfold Wz; omega) (Or.inr h1)
  exact {
    wb := hw
    one := by rw [hr 1001 (by omega) (by omega)]; exact hl.one
    kk := h16
    lZ := by rw [g 1010 (by omega) (by omega) (by omega)]; omega
    l0 := by rw [g 1010 (by omega) (by omega) (by omega), g 1011 (by omega) (by omega) (by omega)]; exact l0
    l1 := by rw [g 1011 (by omega) (by omega) (by omega), g 1012 (by omega) (by omega) (by omega)]; exact l1
    l2 := by rw [g 1012 (by omega) (by omega) (by omega), g 1013 (by omega) (by omega) (by omega)]; exact l2
    l3 := by rw [g 1013 (by omega) (by omega) (by omega), g 1014 (by omega) (by omega) (by omega)]; exact l3
    l4 := by rw [g 1014 (by omega) (by omega) (by omega), g 1015 (by omega) (by omega) (by omega)]; exact l4
    l5 := by rw [g 1015 (by omega) (by omega) (by omega), g 1017 (by omega) (by omega) (by omega)]; exact l5
    l6 := by rw [g 1017 (by omega) (by omega) (by omega), g 1018 (by omega) (by omega) (by omega)]; exact l6
    l7 := by rw [g 1018 (by omega) (by omega) (by omega), g 1019 (by omega) (by omega) (by omega)]; exact l7
    l8 := by rw [g 1019 (by omega) (by omega) (by omega)]; exact l8
    ofs := fun v hv => by
      rw [g 1010 (by omega) (by omega) (by omega), hfar _ (by omega) (by omega)]; exact hl.ofs v hv
    tl := fun x hx => by
      rw [g 1011 (by omega) (by omega) (by omega), hfar _ (by omega) (by omega)]; exact hl.tl x hx
    rv := fun x hx => by
      rw [g 1012 (by omega) (by omega) (by omega), hfar _ (by omega) (by omega)]; exact hl.rv x hx
    ro := fun x hx => by
      rw [g 1013 (by omega) (by omega) (by omega), hfar _ (by omega) (by omega)]; exact hp.ro x hx
    wt := fun x hx => by
      rw [g 1014 (by omega) (by omega) (by omega), hfar _ (by omega) (by omega)]; exact hl.wt x hx
    L := fun j hj => by rw [g 1015 (by omega) (by omega) (by omega)]; exact hL j hj
    lab := fun x hx => by
      rw [g 1017 (by omega) (by omega) (by omega), hfar' _ (by omega)]; exact hp.lab x hx
    rk := fun x hx => by
      rw [g 1018 (by omega) (by omega) (by omega), hfar' _ (by omega)]; exact hp.rk x hx
    zero := fun a ha => by
      rw [hm a (by unfold Wz; omega) (Or.inl (by omega))]; exact hp.zero a ha
    zreg := fun r hr' => by rw [hr r (by omega) (by omega)]; exact hp.zreg r hr'
    rz := fun r hr' => by rw [hrr]; exact hp.rz r hr'
    rmz := fun a ha => by rw [hrm]; exact hp.rmz a ha
    big := le_trans (Nat.mul_le_mul_left 2 (bB_mono (card_le_card hCU) (mI_mono hCU)
      (sum_le_sum_of_subset_of_nonneg hCU fun _ _ _ => Nat.zero_le _))) hp.big }

end Piece

end PlanarSeparator
