module

public import PlanarSeparator.Machine.CompMarks

/-!
# The separator of the components on the machine: no heavy component

When no component weighs more than `2/3` of `U`, the first part is `lightA`
(`PlanarSeparator.lightA_eq`): the scan `scanP` adds the weights of the components of the
vertices of the list of `U` in order (each once, with the seen flags at `aSn`) until a third of
the weight of `U` is reached; `modeP` decides between the last component and the union; `mPass`
writes the marks `1` (first part) and `2` (the rest).

* `SeenAt`, `ScanOK`: the seen flags and the state of the scan.
* **`scanP_exec`**, **`modeP_exec`**, **`mPass_exec`**.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarSeparator

namespace Piece

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

variable {N : ℕ} {G : SimpleGraph (Fin N)} [DecidableRel G.Adj] {U : Finset (Fin N)}
  {w : Fin N → ℕ} {W : ℕ} {P : Input}

/-! ### The seen flags -/

/-- The seen flags of the components meeting `S`: `sn j = 1` iff some vertex of `S` has the label
`j + 1`. -/
def SeenAt (lab sn : ℕ → ℕ) (S : Finset (Fin N)) : Prop :=
  ∀ j ≤ N, sn j = if ∃ y ∈ S, lab y = j + 1 then 1 else 0

variable {nc : ℕ} {lab cw : ℕ → ℕ}

theorem BInv.lab_eq_iff (hB : BInv G U w #U nc lab cw) {x y : Fin N} (hx : x ∈ U) (hy : y ∈ U) :
    lab y = lab x ↔ y ∈ comp G U x := by
  rw [hB.same x (val_mem_UN.2 hx) y (val_mem_UN.2 hy) (hB.final (val_mem_UN.2 hx)), cN_val]

theorem BInv.lab_le (hB : BInv G U w #U nc lab cw) {x : ℕ} (hx : x ∈ UN U) : lab x ≤ N + 1 := by
  have h1 := (hB.rng x hx (by have := hB.final hx; omega)).2
  have := hB.ncle; have := card_le_N U; omega

theorem SeenAt.seen_iff (hB : BInv G U w #U nc lab cw) {sn : ℕ → ℕ} {i : ℕ}
    (hS : SeenAt lab sn (pU G U i)) {x : Fin N} (hx : x ∈ U) :
    sn (lab x - 1) = if x ∈ pU G U i then 1 else 0 := by
  have h2 := hB.final (val_mem_UN.2 hx)
  rw [hS _ (by have := hB.lab_le (val_mem_UN.2 hx); omega), show lab x - 1 + 1 = lab x by omega]
  congr 1
  apply propext
  rw [mem_pU_iff_comp hx]
  constructor
  · rintro ⟨y, hy, e⟩; exact ⟨y, hy, (hB.lab_eq_iff hx (pU_subset U i hy)).1 e⟩
  · rintro ⟨y, hy, e⟩; exact ⟨y, hy, (hB.lab_eq_iff hx (pU_subset U i hy)).2 e⟩

theorem SeenAt.add (hB : BInv G U w #U nc lab cw) {sn sn' : ℕ → ℕ} {S : Finset (Fin N)}
    (hS : SeenAt lab sn S) {x : Fin N} (hx : x ∈ U)
    (h1 : sn' (lab x - 1) = 1) (ho : ∀ j, j ≠ lab x - 1 → sn' j = sn j) :
    SeenAt lab sn' (S ∪ comp G U x) := by
  have h2 := hB.final (val_mem_UN.2 hx)
  intro j hj
  by_cases e : j = lab x - 1
  · subst e
    rw [h1, iteT ⟨x, mem_union_right _ (mem_comp_self hx), by omega⟩]
  · rw [ho j e, hS j hj]
    congr 1
    apply propext
    constructor
    · rintro ⟨y, hy, ey⟩; exact ⟨y, mem_union_left _ hy, ey⟩
    · rintro ⟨y, hy, ey⟩
      rcases mem_union.1 hy with hy | hy
      · exact ⟨y, hy, ey⟩
      · have := (hB.lab_eq_iff hx (comp_subset _ _ hy)).2 hy
        omega

theorem pU_succ_of_mem {i : ℕ} (hi : i < (ul U).length) (h : (ul U)[i] ∈ pU G U i) :
    pU G U (i + 1) = pU G U i := by
  rw [pU_succ U hi]
  exact union_eq_left.2 (comp_subset_pU h (mem_comp_self (ul_mem U hi)))

theorem disjoint_pU {i : ℕ} {x : Fin N} (hx : x ∈ U) (h : x ∉ pU G U i) :
    Disjoint (pU G U i) (comp G U x) := by
  rw [disjoint_left]
  intro y hy hyx
  exact h (comp_subset_pU hy hyx (mem_comp_self hx))

theorem pU_all : pU G U #U = U := by
  apply subset_antisymm (pU_subset U _)
  intro x hx
  obtain ⟨l, hl, rfl⟩ := exists_ul U hx
  exact mem_pU.2 ⟨l, hl, by rw [← ul_length]; exact hl, mem_comp_self (ul_mem U hl)⟩

/-! ### The scan -/

/-- The weight of a vertex set. -/
abbrev wt (w : Fin N → ℕ) (S : Finset (Fin N)) : ℕ := ∑ v ∈ S, w v

variable (G) in
/-- **The state of the scan after `i` vertices**: not found yet (the prefixes below a third, the
accumulated weight and the seen flags of `pU U i`), found at `l`, or `U` of weight `0`. -/
def ScanOK (U : Finset (Fin N)) (w : Fin N → ℕ) (lab sn : ℕ → ℕ) (i f acc kj : ℕ) : Prop :=
  (0 < wt w U ∧ f = 0 ∧ kj = 0 ∧ (∀ l < i, 3 * wt w (pU G U (l + 1)) < wt w U) ∧
      acc = wt w (pU G U i) ∧ SeenAt lab sn (pU G U i)) ∨
    (0 < wt w U ∧ f = 1 ∧ ∃ l < i, l < #U ∧ (∀ l' < l, 3 * wt w (pU G U (l' + 1)) < wt w U) ∧
      wt w U ≤ 3 * wt w (pU G U (l + 1)) ∧ kj = lab (lv U l) - 1 ∧
      SeenAt lab sn (pU G U (l + 1))) ∨
    (wt w U = 0 ∧ f = 1 ∧ kj = 0 ∧ SeenAt lab sn (∅ : Finset (Fin N)))

/-- A new component: seen, its weight added; found when a third is reached. -/
def sNew : Stmt :=
  .seq (block [.storeN 1118 1001, .addN 1118 1104 1119, .loadN 1125 1118, .addN 1133 1133 1125,
    .addN 1126 1133 1133, .addN 1126 1126 1133])
    (.ifLtN 1126 1120 .skip (block [.copyN 1132 1001, .copyN 1134 1119]))

/-- The test of the `i`-th vertex of the list while not found. -/
def sTest : Stmt :=
  .seq (block pfx) (.seq (block [.subN 1119 1119 1001, .addN 1118 1105 1119, .loadN 1125 1118])
    (.ifLtN 1125 1001 sNew .skip))

/-- **The scan of the light components.** -/
def scanP : Stmt :=
  .seq (block [.constN 1132 0, .constN 1133 0, .constN 1134 0, .constN 1110 0])
    (.seq (.ifLtN 0 1120 .skip (.instr (.copyN 1132 1001)))
      (.whileLtN 1110 1101 (.seq (.ifLtN 1132 1001 sTest .skip) (.instr (.addN 1110 1110 1001)))))

theorem scanP_exec {c : Config} (hl : CLay G U w W c) {d : Config} (env : Env N W c d)
    (hB : BInv G U w #U nc (labF c d) (cwF c d)) (h20 : d.nreg 1120 = ∑ v ∈ U, w v) :
    ∃ d' k, Exec P W scanP d d' k ∧ WordsBounded W d' ∧
      (∀ r, r < 1110 ∨ r = 1120 ∨ r = 1130 → d'.nreg r = d.nreg r) ∧
      ScanOK G U w (labF c d) (fun j => d'.nmem (c.nreg 1105 + j)) #U (d'.nreg 1132)
        (d'.nreg 1133) (d'.nreg 1134) ∧
      (∀ a, a < c.nreg 1105 ∨ c.nreg 1105 + N + 1 ≤ a → d'.nmem a = d.nmem a) ∧
      k ≤ 22 * #U + 9 := by
  have lU := hl.lU; have lC := hl.lC; have lQ := hl.lQ; have lW := hl.lW; have lS := hl.lS
  have l0 := hl.l0; have l1 := hl.l1; have l2 := hl.l2; have l3 := hl.l3; have l4 := hl.l4
  have l5 := hl.l5; have l6 := hl.l6; have l7 := hl.l7; have l8 := hl.l8
  have hNW := hl.NW
  have hU := card_le_N U
  have hsw := hl.sw
  have f := env.fix
  set aS := c.nreg 1105
  set lab := labF c d
  set wU := ∑ v ∈ U, w v
  have hsn0 : ∀ j ≤ N, d.nmem (aS + j) = 0 := fun j hj => by
    rw [env.fr _ (by unfold Wz; omega)]; exact hl.sn j hj
  obtain ⟨d₀, k₀, e₀, hw₀, a32, a33, a34, a10, q₀, m₀, hk₀⟩ : ∃ d₀ k₀, Exec P W
      (block [.constN 1132 0, .constN 1133 0, .constN 1134 0, .constN 1110 0]) d d₀ k₀ ∧
      WordsBounded W d₀ ∧ d₀.nreg 1132 = 0 ∧ d₀.nreg 1133 = 0 ∧ d₀.nreg 1134 = 0 ∧
      d₀.nreg 1110 = 0 ∧
      (∀ r, r ≠ 1132 → r ≠ 1133 → r ≠ 1134 → r ≠ 1110 → d₀.nreg r = d.nreg r) ∧
      d₀.nmem = d.nmem ∧ k₀ = 4 := by
    have hw := env.wb
    exec_block
    · omega
    · omega
    · omega
    · omega
    · exact ⟨‹WordsBounded _ _›, by simp, by simp, by simp, by simp,
        fun r h1 h2 h3 h4 => by simp [h1, h2, h3, h4], rfl, rfl⟩
  let I : ℕ → Config → Prop := fun i d' => WordsBounded W d' ∧ d'.nreg 1110 = i ∧
    d'.nreg 1101 = #U ∧ (∀ r, r < 1110 ∨ r = 1120 ∨ r = 1130 → d'.nreg r = d.nreg r) ∧
    ScanOK G U w lab (fun j => d'.nmem (aS + j)) i (d'.nreg 1132) (d'.nreg 1133) (d'.nreg 1134) ∧
    (∀ a, a < aS ∨ aS + N + 1 ≤ a → d'.nmem a = d.nmem a)
  have hseen0 : SeenAt lab (fun j => d₀.nmem (aS + j)) (∅ : Finset (Fin N)) := fun j hj => by
    simp only [m₀, hsn0 j hj, notMem_empty, false_and, exists_false, iteF not_false]
  have q₀' : ∀ r, r < 1110 ∨ r = 1120 ∨ r = 1130 → d₀.nreg r = d.nreg r := fun r hr =>
    q₀ r (by omega) (by omega) (by omega) (by omega)
  have b20 : d₀.nreg 1120 = wU := by rw [q₀' 1120 (by omega)]; exact h20
  have b00 : d₀.nreg 0 = 0 := by rw [q₀' 0 (by omega), f 0 (by omega)]; exact hl.r0
  have b01 : d₀.nreg 1001 = 1 := by rw [q₀' 1001 (by omega), f 1001 (by omega)]; exact hl.one
  have b1101 : d₀.nreg 1101 = #U := by rw [q₀' 1101 (by omega), f 1101 (by omega)]; exact hl.uu
  obtain ⟨d₁, k₁, e₁, hI₁, hk₁⟩ : ∃ d₁ k₁, Exec P W (.ifLtN 0 1120 .skip
      (.instr (.copyN 1132 1001))) d₀ d₁ k₁ ∧ I 0 d₁ ∧ k₁ ≤ 3 := by
    by_cases hpos : d₀.nreg 0 < d₀.nreg 1120
    · refine ⟨d₀, _, .ifLtN_true hpos (.skip hw₀), ⟨hw₀, a10, b1101, q₀', Or.inl ⟨?_, a32, a34,
        fun l hl => absurd hl (Nat.not_lt_zero _), ?_, ?_⟩, fun a _ => by rw [m₀]⟩, by omega⟩
      · rw [b00, b20] at hpos; exact hpos
      · rw [a33, pU_zero]; rfl
      · rw [pU_zero]; exact hseen0
    · have e := Exec.copyN (P := P) hw₀ 1132 1001
      refine ⟨_, _, .ifLtN_false hpos e, ⟨e.wb_right, by simp [a10], by simp [b1101],
        fun r hr => by simp [show r ≠ 1132 by omega]; exact q₀' r hr,
        Or.inr (Or.inr ⟨?_, by simp [b01], by simp [a34], hseen0⟩), fun a _ => by simp [m₀]⟩,
        by omega⟩
      rw [b00, b20] at hpos; simp only [wt]; omega
  obtain ⟨d₂, k₂, e₂, hI₂, hk₂⟩ := Exec.forN (P := P) (W := W) (ri := 1110) (rN := 1101)
    (N := #U) (lo := 0) (B := 20) (body := .seq (.ifLtN 1132 1001 sTest .skip)
      (.instr (.addN 1110 1110 1001))) I (fun i d' h => ⟨h.1, h.2.1, h.2.2.1⟩)
    (fun i d' h hi => by
      obtain ⟨hw, h10, h1101, hq, hok, hfr⟩ := h
      have g01 : d'.nreg 1001 = 1 := by rw [hq 1001 (by omega), f 1001 (by omega)]; exact hl.one
      have hlast : ∀ d₃ : Config, WordsBounded W d₃ → d₃.nreg 1110 = i → d₃.nreg 1001 = 1 →
          ∃ d₄, Exec P W (.instr (.addN 1110 1110 1001)) d₃ d₄ 1 ∧ WordsBounded W d₄ ∧
            d₄.nreg 1110 = i + 1 ∧ (∀ r, r ≠ 1110 → d₄.nreg r = d₃.nreg r) ∧
            d₄.nmem = d₃.nmem := by
        intro d₃ hw₃ h10' h01'
        have e := Exec.addN (P := P) hw₃ 1110 1110 1001 (by rw [h10', h01']; omega)
        exact ⟨_, e, e.wb_right, by simp [h10', h01'], fun r hr => by simp [hr], rfl⟩
      by_cases hf : d'.nreg 1132 < d'.nreg 1001
      swap
      · -- found already (or weight `0`): nothing changes
        obtain ⟨d₄, e₄, hw₄, h10', q₄, m₄⟩ := hlast d' hw h10 g01
        refine ⟨d₄, _, .seq (.ifLtN_false hf (.skip hw)) e₄, ⟨hw₄, h10', ?_,
          fun r hr => by rw [q₄ r (by omega)]; exact hq r hr, ?_,
          fun a ha => by rw [m₄]; exact hfr a ha⟩, by omega⟩
        · rw [q₄ 1101 (by omega)]; exact h1101
        rw [q₄ 1132 (by omega), q₄ 1133 (by omega), q₄ 1134 (by omega), m₄]
        rcases hok with ⟨-, h0, -⟩ | ⟨h1, h2, l, hl, h3⟩ | h'
        · omega
        · exact Or.inr (Or.inl ⟨h1, h2, l, by omega, h3⟩)
        · exact Or.inr (Or.inr h')
      -- not found yet
      have hA : 0 < wt w U ∧ d'.nreg 1132 = 0 ∧ d'.nreg 1134 = 0 ∧
          (∀ l < i, 3 * wt w (pU G U (l + 1)) < wt w U) ∧ d'.nreg 1133 = wt w (pU G U i) ∧
          SeenAt lab (fun j => d'.nmem (aS + j)) (pU G U i) := by
        rcases hok with h' | ⟨-, h2, -⟩ | ⟨-, h2, -⟩
        · exact h'
        · omega
        · omega
      obtain ⟨hpos, h32, h34, hbelow, h33, hseen⟩ := hA
      have hi' : i < (ul U).length := by rw [ul_length]; exact hi
      obtain ⟨xF, hxF⟩ : ∃ xF, xF = (ul U)[i] := ⟨_, rfl⟩
      have hxU : xF ∈ U := hxF ▸ ul_mem U hi'
      have hxv : lv U i = (xF : ℕ) := by rw [hxF]; exact lv_ul U hi'
      have hxUN := lv_mem_UN U hi
      have hxN := lt_of_mem_UN hxUN
      have hlab2 := hB.final hxUN
      have hlabN := hB.lab_le hxUN
      have mU : d'.nmem (c.nreg 1100 + i) = lv U i := by
        rw [hfr _ (Or.inl (by omega)), env.fr _ (by unfold Wz; omega)]; exact hl.ul i hi
      have mC : d'.nmem (c.nreg 1102 + lv U i) = lab (lv U i) := hfr _ (Or.inl (by omega))
      obtain ⟨d₃, e₃, hw₃, b14, b18, b19, q₃, m₃⟩ := pfx_exec (P := P) hw
        (by rw [hq 1100 (by omega), f 1100 (by omega)])
        (by rw [hq 1102 (by omega), f 1102 (by omega)]) h10 mU (by omega) (by omega)
      rw [mC] at b19
      have hsj : d'.nmem (aS + (lab (lv U i) - 1)) = if xF ∈ pU G U i then 1 else 0 := by
        have := hseen.seen_iff hB hxU
        rw [← hxv] at this; exact this
      have c01 : d₃.nreg 1001 = 1 := by rw [q₃ 1001 (by omega) (by omega) (by omega), g01]
      have c05 : d₃.nreg 1105 = aS := by
        rw [q₃ 1105 (by omega) (by omega) (by omega), hq 1105 (by omega), f 1105 (by omega)]
      obtain ⟨d₄, k₄, e₄, hw₄, a19, a18, a25, q₄, m₄, hk₄⟩ : ∃ d₄ k₄, Exec P W
          (block [.subN 1119 1119 1001, .addN 1118 1105 1119, .loadN 1125 1118]) d₃ d₄ k₄ ∧
          WordsBounded W d₄ ∧ d₄.nreg 1119 = lab (lv U i) - 1 ∧
          d₄.nreg 1118 = aS + (lab (lv U i) - 1) ∧
          d₄.nreg 1125 = (if xF ∈ pU G U i then 1 else 0) ∧
          (∀ r, r ≠ 1119 → r ≠ 1118 → r ≠ 1125 → d₄.nreg r = d₃.nreg r) ∧ d₄.nmem = d₃.nmem ∧
          k₄ = 3 := by
        exec_block
        · config_simp; rw [c05, b19, c01]; omega
        · refine ⟨‹WordsBounded _ _›, ?_, ?_, ?_, fun r h1 h2 h3 => by simp [h1, h2, h3], rfl,
            rfl⟩
          · simp only [upd_apply, Nat.reduceEqDiff, ↓reduceIte]; rw [b19, c01]
          · simp only [upd_apply, Nat.reduceEqDiff, ↓reduceIte]; rw [b19, c01, c05]
          · simp only [upd_apply, ↓reduceIte]; rw [b19, c01, c05, m₃, hsj]
      have qq : ∀ r, r ≠ 1119 → r ≠ 1118 → r ≠ 1125 → r ≠ 1114 → d₄.nreg r = d'.nreg r :=
        fun r a b c' e => by rw [q₄ r a b c', q₃ r b e a]
      have hm₄ : d₄.nmem = d'.nmem := by rw [m₄, m₃]
      by_cases hseen1 : xF ∈ pU G U i
      · -- seen: nothing changes
        have t : ¬ d₄.nreg 1125 < d₄.nreg 1001 := by
          rw [a25, iteT hseen1, qq 1001 (by omega) (by omega) (by omega) (by omega), g01]; omega
        obtain ⟨d₅, e₅, hw₅, h10', q₅, m₅⟩ := hlast d₄ hw₄
          (by rw [qq 1110 (by omega) (by omega) (by omega) (by omega), h10])
          (by rw [qq 1001 (by omega) (by omega) (by omega) (by omega), g01])
        have q5 : ∀ r, r ≠ 1119 → r ≠ 1118 → r ≠ 1125 → r ≠ 1114 → r ≠ 1110 →
            d₅.nreg r = d'.nreg r := fun r a b c' e g => by rw [q₅ r g, qq r a b c' e]
        have hpU : pU G U (i + 1) = pU G U i := pU_succ_of_mem hi' (hxF ▸ hseen1)
        refine ⟨d₅, _, .seq (.ifLtN_true hf (.seq e₃ (.seq e₄ (.ifLtN_false t (.skip hw₄)))))
          e₅, ⟨hw₅, h10', ?_, fun r hr => ?_, ?_, fun a ha => by rw [m₅, hm₄]; exact hfr a ha⟩,
          by omega⟩
        · rw [q5 1101 (by omega) (by omega) (by omega) (by omega) (by omega)]; exact h1101
        · rw [q5 r (by omega) (by omega) (by omega) (by omega) (by omega)]; exact hq r hr
        rw [q5 1132 (by omega) (by omega) (by omega) (by omega) (by omega),
          q5 1133 (by omega) (by omega) (by omega) (by omega) (by omega),
          q5 1134 (by omega) (by omega) (by omega) (by omega) (by omega), m₅, hm₄]
        refine Or.inl ⟨hpos, h32, h34, fun l hl => ?_, by rw [hpU]; exact h33,
          by rw [hpU]; exact hseen⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hl with hl | rfl
        · exact hbelow l hl
        · rw [hpU]
          rcases Nat.eq_zero_or_pos l with rfl | hl0
          · rw [pU_zero]; simpa using hpos
          · have := hbelow (l - 1) (by omega)
            rwa [show l - 1 + 1 = l by omega] at this
      · -- a new component
        have t : d₄.nreg 1125 < d₄.nreg 1001 := by
          rw [a25, iteF hseen1, qq 1001 (by omega) (by omega) (by omega) (by omega), g01]; omega
        set j := lab (lv U i) - 1 with hj
        have hjN : j ≤ N := by omega
        have hcwj : d₄.nmem (c.nreg 1104 + j) = wt w (comp G U xF) := by
          rw [hm₄, hfr _ (Or.inl (by omega))]
          have := hB.wt _ hxUN hlab2
          unfold cwF at this; rw [this, hxv, sum_cN]
        have hdisj := disjoint_pU (G := G) (i := i) hxU hseen1
        have hpU1 : wt w (pU G U (i + 1)) = wt w (pU G U i) + wt w (comp G U xF) := by
          unfold wt; rw [pU_succ U hi', ← hxF, sum_union hdisj]
        have hle : wt w (pU G U (i + 1)) ≤ wU :=
          sum_le_sum_of_subset_of_nonneg (pU_subset U _) (fun _ _ _ => Nat.zero_le _)
        have c04 : d₄.nreg 1104 = c.nreg 1104 := by
          rw [qq 1104 (by omega) (by omega) (by omega) (by omega), hq 1104 (by omega),
            f 1104 (by omega)]
        have c33 : d₄.nreg 1133 = wt w (pU G U i) := by
          rw [qq 1133 (by omega) (by omega) (by omega) (by omega), h33]
        have c01' : d₄.nreg 1001 = 1 := by
          rw [qq 1001 (by omega) (by omega) (by omega) (by omega), g01]
        obtain ⟨d₅, k₅, e₅, hw₅, a26, a33', q₅, m₅, hk₅⟩ : ∃ d₅ k₅, Exec P W
            (block [.storeN 1118 1001, .addN 1118 1104 1119, .loadN 1125 1118,
              .addN 1133 1133 1125, .addN 1126 1133 1133, .addN 1126 1126 1133]) d₄ d₅ k₅ ∧
            WordsBounded W d₅ ∧ d₅.nreg 1126 = 3 * wt w (pU G U (i + 1)) ∧
            d₅.nreg 1133 = wt w (pU G U (i + 1)) ∧
            (∀ r, r ≠ 1118 → r ≠ 1125 → r ≠ 1126 → r ≠ 1133 → d₅.nreg r = d₄.nreg r) ∧
            d₅.nmem = upd d₄.nmem (aS + j) 1 ∧ k₅ = 6 := by
          exec_block
          · config_simp; rw [c04, a19]; omega
          · config_simp
            rw [c04, a19, a18, c01', upd_other _ _ _ (by omega), hcwj, c33]; omega
          · config_simp
            rw [c04, a19, a18, c01', upd_other _ _ _ (by omega), hcwj, c33]; omega
          · config_simp
            rw [c04, a19, a18, c01', upd_other _ _ _ (by omega), hcwj, c33]; omega
          · refine ⟨‹WordsBounded _ _›, ?_, ?_, fun r h1 h2 h3 h4 => by simp [h1, h2, h3, h4],
              ?_, rfl⟩
            · simp only [upd_apply, ↓reduceIte]
              rw [c04, a19, a18, c01', iteF (show ¬ (c.nreg 1104 + j = aS + j) by omega), hcwj,
                c33, hpU1]; ring
            · simp only [upd_apply, Nat.reduceEqDiff, ↓reduceIte]
              rw [c04, a19, a18, c01', iteF (show ¬ (c.nreg 1104 + j = aS + j) by omega), hcwj,
                c33, hpU1]
            · simp only [a18, c01']
        have hseen' : SeenAt lab (fun j' => d₅.nmem (aS + j')) (pU G U (i + 1)) := by
          rw [pU_succ U hi', ← hxF]
          refine hseen.add hB hxU (sn' := fun j' => d₅.nmem (aS + j')) ?_ fun j' hj' => ?_
          · simp only [m₅, ← hxv]; rw [← hj, upd_same]
          · simp only [m₅, hm₄]
            rw [upd_other _ _ _ (by rw [← hxv] at hj'; omega)]
        have q45 : ∀ r, r ≠ 1118 → r ≠ 1125 → r ≠ 1126 → r ≠ 1133 → r ≠ 1119 → r ≠ 1114 →
            d₅.nreg r = d'.nreg r := fun r a b c' e g h => by rw [q₅ r a b c' e, qq r g a b h]
        have c20 : d₅.nreg 1120 = wU := by
          rw [q45 1120 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
            hq 1120 (by omega), h20]
        have hmem5 : ∀ a, a < aS ∨ aS + N + 1 ≤ a → d₅.nmem a = d.nmem a := fun a ha => by
          rw [m₅, upd_other _ _ _ (by omega), hm₄]; exact hfr a ha
        by_cases hlt : d₅.nreg 1126 < d₅.nreg 1120
        · obtain ⟨d₆, e₆, hw₆, h10', q₆, m₆⟩ := hlast d₅ hw₅
            (by rw [q45 1110 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
              h10])
            (by rw [q45 1001 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
              g01])
          rw [a26, c20] at hlt
          refine ⟨d₆, _, .seq (.ifLtN_true hf (.seq e₃ (.seq e₄ (.ifLtN_true t (.seq e₅
            (.ifLtN_true (by rw [a26, c20]; exact hlt) (.skip hw₅))))))) e₆, ⟨hw₆, h10', ?_,
            fun r hr => ?_, ?_, fun a ha => by rw [m₆]; exact hmem5 a ha⟩, by omega⟩
          · rw [q₆ 1101 (by omega), q45 1101 (by omega) (by omega) (by omega) (by omega)
              (by omega) (by omega)]; exact h1101
          · rw [q₆ r (by omega), q45 r (by omega) (by omega) (by omega) (by omega) (by omega)
              (by omega)]; exact hq r hr
          · rw [q₆ 1132 (by omega), q₆ 1133 (by omega), q₆ 1134 (by omega), m₆, a33',
              q45 1132 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
              q45 1134 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
            refine Or.inl ⟨hpos, h32, h34, fun l hl => ?_, rfl, hseen'⟩
            rcases Nat.lt_succ_iff_lt_or_eq.1 hl with hl | rfl
            · exact hbelow l hl
            · exact hlt
        · have e6 := Exec.copyN (P := P) hw₅ 1132 1001
          have e7 := Exec.copyN (P := P) e6.wb_right 1134 1119
          obtain ⟨d₆, e₆, hw₆, h10', q₆, m₆⟩ := hlast _ e7.wb_right
            (by simp; rw [q45 1110 (by omega) (by omega) (by omega) (by omega) (by omega)
              (by omega), h10])
            (by simp; rw [q45 1001 (by omega) (by omega) (by omega) (by omega) (by omega)
              (by omega), g01])
          rw [a26, c20] at hlt
          refine ⟨d₆, _, .seq (.ifLtN_true hf (.seq e₃ (.seq e₄ (.ifLtN_true t (.seq e₅
            (.ifLtN_false (by rw [a26, c20]; exact hlt) (.seq e6 (.seq e7 (.skip e7.wb_right)))))))))
            e₆, ⟨hw₆, h10', ?_, fun r hr => ?_, ?_, fun a ha => by rw [m₆]; exact hmem5 a ha⟩,
            by omega⟩
          · rw [q₆ 1101 (by omega)]; simp
            rw [q45 1101 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
            exact h1101
          · rw [q₆ r (by omega)]; simp [show r ≠ 1132 by omega, show r ≠ 1134 by omega]
            rw [q45 r (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
            exact hq r hr
          · rw [q₆ 1132 (by omega), q₆ 1133 (by omega), q₆ 1134 (by omega), m₆]
            simp only [upd_apply, Nat.reduceEqDiff, ↓reduceIte]
            rw [q₅ 1119 (by omega) (by omega) (by omega) (by omega), a19,
              q₅ 1001 (by omega) (by omega) (by omega) (by omega), c01']
            refine Or.inr (Or.inl ⟨hpos, rfl, i, Nat.lt_succ_self _, hi, hbelow, ?_, rfl,
              hseen'⟩)
            show wU ≤ _
            omega)
    (Nat.zero_le _) hI₁
  obtain ⟨hw₂, -, -, hq₂, hok₂, hfr₂⟩ := hI₂
  refine ⟨d₂, k₀ + (k₁ + k₂), .seq e₀ (.seq e₁ e₂), hw₂, hq₂, hok₂, hfr₂, by omega⟩

/-- **The mode**: `1135 = 1` iff the component found (`1134 ≠ 0`) weighs at least a third. -/
def modeP : Stmt :=
  .seq (.instr (.constN 1135 0)) (.ifLtN 0 1134 (.seq (block [.addN 1118 1104 1134,
    .loadN 1125 1118, .addN 1126 1125 1125, .addN 1126 1126 1125])
    (.ifLtN 1126 1120 .skip (.instr (.copyN 1135 1001)))) .skip)

theorem modeP_exec {d : Config} (hw : WordsBounded W d) {kj aCw wU : ℕ}
    (h34 : d.nreg 1134 = kj) (h04 : d.nreg 1104 = aCw) (h20 : d.nreg 1120 = wU)
    (h01 : d.nreg 1001 = 1) (h00 : d.nreg 0 = 0) (hk : aCw + kj ≤ W)
    (hv : 3 * d.nmem (aCw + kj) ≤ W) :
    ∃ d' k, Exec P W modeP d d' k ∧ WordsBounded W d' ∧
      d'.nreg 1135 = (if 0 < kj ∧ wU ≤ 3 * d.nmem (aCw + kj) then 1 else 0) ∧
      (∀ r, r ≠ 1118 → r ≠ 1125 → r ≠ 1126 → r ≠ 1135 → d'.nreg r = d.nreg r) ∧
      d'.nmem = d.nmem ∧ k ≤ 9 := by
  have e0 := Exec.constN (P := P) hw 1135 0 (Nat.zero_le _)
  set d₀ := { d with nreg := upd d.nreg 1135 0 }
  have hw₀ : WordsBounded W d₀ := e0.wb_right
  have q₀ : ∀ r, r ≠ 1135 → d₀.nreg r = d.nreg r := fun r hr => by simp [d₀, hr]
  have m₀ : d₀.nmem = d.nmem := rfl
  by_cases hkj : d₀.nreg 0 < d₀.nreg 1134
  · have t0 := hkj
    rw [q₀ 0 (by omega), q₀ 1134 (by omega), h00, h34] at hkj
    obtain ⟨d₁, k₁, e₁, hw₁, a26, q₁, m₁, hk₁⟩ : ∃ d₁ k₁, Exec P W (block [.addN 1118 1104 1134,
        .loadN 1125 1118, .addN 1126 1125 1125, .addN 1126 1126 1125]) d₀ d₁ k₁ ∧
        WordsBounded W d₁ ∧ d₁.nreg 1126 = 3 * d.nmem (aCw + kj) ∧
        (∀ r, r ≠ 1118 → r ≠ 1125 → r ≠ 1126 → d₁.nreg r = d₀.nreg r) ∧ d₁.nmem = d₀.nmem ∧
        k₁ = 4 := by
      exec_block
      · rw [q₀ 1104 (by omega), q₀ 1134 (by omega), h04, h34]; exact hk
      · config_simp; rw [q₀ 1104 (by omega), q₀ 1134 (by omega), h04, h34, m₀]; omega
      · config_simp; rw [q₀ 1104 (by omega), q₀ 1134 (by omega), h04, h34, m₀]; omega
      · refine ⟨‹WordsBounded _ _›, ?_, fun r h1 h2 h3 => by simp [h1, h2, h3], rfl, rfl⟩
        simp only [upd_apply, ↓reduceIte]
        rw [q₀ 1104 (by omega), q₀ 1134 (by omega), h04, h34]
        rw [m₀]; ring
    have b20 : d₁.nreg 1120 = wU := by
      rw [q₁ 1120 (by omega) (by omega) (by omega), q₀ 1120 (by omega), h20]
    have b35 : d₁.nreg 1135 = 0 := by rw [q₁ 1135 (by omega) (by omega) (by omega)]; simp [d₀]
    by_cases hlt : d₁.nreg 1126 < d₁.nreg 1120
    · refine ⟨d₁, _, .seq e0 (.ifLtN_true t0 (.seq e₁ (.ifLtN_true hlt (.skip hw₁)))), hw₁, ?_,
        fun r h1 h2 h3 h4 => ?_,
        by rw [m₁], by omega⟩
      · rw [b35, a26, b20] at *
        rw [iteF (by omega)]
      · rw [q₁ r h1 h2 h3, q₀ r h4]
    · have e2 := Exec.copyN (P := P) hw₁ 1135 1001
      refine ⟨_, _, .seq e0 (.ifLtN_true t0 (.seq e₁ (.ifLtN_false hlt e2))), e2.wb_right, ?_,
        fun r h1 h2 h3 h4 => ?_,
        by simp [m₁, m₀], by omega⟩
      · rw [a26, b20] at hlt
        simp only [upd_same]
        rw [q₁ 1001 (by omega) (by omega) (by omega), q₀ 1001 (by omega), h01,
          iteT ⟨hkj, by omega⟩]
      · simp [h4]; rw [q₁ r h1 h2 h3, q₀ r h4]
  · refine ⟨d₀, _, .seq e0 (.ifLtN_false hkj (.skip hw₀)), hw₀, ?_, fun r h1 h2 h3 h4 => q₀ r h4,
      rfl, by omega⟩
    rw [q₀ 0 (by omega), q₀ 1134 (by omega), h00, h34] at hkj
    simp [d₀, iteF (show ¬ (0 < kj ∧ wU ≤ 3 * d.nmem (aCw + kj)) by omega)]

/-- The body of the pass writing the marks of the light case. -/
def mBody : Stmt :=
  .seq (block pfx) (.seq (block [.subN 1119 1119 1001, .addN 1118 1105 1119, .loadN 1125 1118,
    .addN 1118 1019 1114, .copyN 1126 1130]) (.seq (.ifLtN 0 1135 (.ifLtN 1119 1134 .skip
      (.ifLtN 1134 1119 .skip (.instr (.copyN 1126 1001))))
      (.ifLtN 0 1125 (.instr (.copyN 1126 1001)) .skip))
    (.seq (.instr (.storeN 1118 1126)) (.instr (.addN 1110 1110 1001)))))

/-- **The marks of the light case**: `1` on the first part, `2` on the rest of `U`. -/
def mPass : Stmt := .seq (.instr (.constN 1110 0)) (.whileLtN 1110 1101 mBody)

/-- The mark of a vertex in the light case. -/
def mkL (lab sn : ℕ → ℕ) (mode kj x : ℕ) : ℕ :=
  if (0 < mode ∧ lab x - 1 = kj) ∨ (¬ 0 < mode ∧ 0 < sn (lab x - 1)) then 1 else 2

theorem mPass_exec {d : Config} (hw : WordsBounded W d) {aU aC aS aM mode kj : ℕ}
    (h01 : d.nreg 1001 = 1) (h0 : d.nreg 0 = 0) (h00 : d.nreg 1100 = aU)
    (h02 : d.nreg 1102 = aC) (h05 : d.nreg 1105 = aS) (h19 : d.nreg 1019 = aM)
    (h1101 : d.nreg 1101 = #U) (h35 : d.nreg 1135 = mode) (h34 : d.nreg 1134 = kj)
    (h30 : d.nreg 1130 = 2) (hU : ∀ l < #U, d.nmem (aU + l) = lv U l)
    (l1 : aU + N ≤ aC) (l2 : aC + N ≤ aS) (l3 : aS + N + 1 ≤ aM) (l4 : aM + N ≤ W)
    (hlab : ∀ x ∈ UN U, d.nmem (aC + x) ≤ N + 1) :
    ∃ d' k, Exec P W mPass d d' k ∧ WordsBounded W d' ∧
      (∀ x < N, d'.nmem (aM + x) = if x ∈ UN U then
        mkL (fun y => d.nmem (aC + y)) (fun j => d.nmem (aS + j)) mode kj x
        else d.nmem (aM + x)) ∧
      (∀ a, a < aM ∨ aM + N ≤ a → d'.nmem a = d.nmem a) ∧
      (∀ r, r ≠ 1110 → r ≠ 1114 → r ≠ 1118 → r ≠ 1119 → r ≠ 1125 → r ≠ 1126 →
        d'.nreg r = d.nreg r) ∧ k ≤ 19 * #U + 3 := by
  have hUN := card_le_N U
  set lab := fun y => d.nmem (aC + y)
  set sn := fun j => d.nmem (aS + j)
  have e0 := Exec.constN (P := P) hw 1110 0 (Nat.zero_le _)
  let I : ℕ → Config → Prop := fun i d' => WordsBounded W d' ∧ d'.nreg 1110 = i ∧
    d'.nreg 1101 = #U ∧
    (∀ r, r ≠ 1110 → r ≠ 1114 → r ≠ 1118 → r ≠ 1119 → r ≠ 1125 → r ≠ 1126 →
      d'.nreg r = d.nreg r) ∧
    (∀ x < N, d'.nmem (aM + x) =
      if ∃ l < i, lv U l = x then mkL lab sn mode kj x else d.nmem (aM + x)) ∧
    (∀ a, a < aM ∨ aM + N ≤ a → d'.nmem a = d.nmem a)
  have hI₀ : I 0 _ := ⟨e0.wb_right, by simp, by simp [h1101],
    fun r hr _ _ _ _ _ => by simp [hr], fun x hx => by simp, fun a _ => rfl⟩
  obtain ⟨d₁, k₁, e₁, hI₁, hk₁⟩ := Exec.forN (P := P) (W := W) (ri := 1110) (rN := 1101)
    (N := #U) (lo := 0) (B := 17) (body := mBody) I (fun i d' h => ⟨h.1, h.2.1, h.2.2.1⟩)
    (fun i d' h hi => by
      obtain ⟨hw', h10, h01', hq, hmk, hfr⟩ := h
      have g : ∀ r, r ≠ 1110 → r ≠ 1114 → r ≠ 1118 → r ≠ 1119 → r ≠ 1125 → r ≠ 1126 →
          d'.nreg r = d.nreg r := hq
      obtain ⟨x, hxdef⟩ : ∃ x, x = lv U i := ⟨_, rfl⟩
      have hxU : x ∈ UN U := hxdef ▸ lv_mem_UN U hi
      have hx := lt_of_mem_UN hxU
      have hlx : lab x ≤ N + 1 := hlab x hxU
      have mU : d'.nmem (aU + i) = x := by
        rw [hfr _ (Or.inl (by omega)), hxdef]; exact hU i hi
      have mC : d'.nmem (aC + x) = lab x := hfr _ (Or.inl (by omega))
      have mS : d'.nmem (aS + (lab x - 1)) = sn (lab x - 1) := hfr _ (Or.inl (by omega))
      obtain ⟨d₂, e₂, hw₂, b14, b18, b19, q₂, m₂⟩ := pfx_exec (P := P) hw'
        (by rw [g 1100 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), h00])
        (by rw [g 1102 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), h02])
        h10 mU (by omega) (by omega)
      rw [mC] at b19
      have q2 : ∀ r, r ≠ 1110 → r ≠ 1114 → r ≠ 1118 → r ≠ 1119 → r ≠ 1125 → r ≠ 1126 →
          d₂.nreg r = d.nreg r := fun r a b c' e f' g' => by rw [q₂ r c' b e, g r a b c' e f' g']
      obtain ⟨d₃, k₃, e₃, hw₃, c19, c25, c18, c26, q₃, m₃, hk₃⟩ : ∃ d₃ k₃, Exec P W
          (block [.subN 1119 1119 1001, .addN 1118 1105 1119, .loadN 1125 1118,
            .addN 1118 1019 1114, .copyN 1126 1130]) d₂ d₃ k₃ ∧ WordsBounded W d₃ ∧
          d₃.nreg 1119 = lab x - 1 ∧ d₃.nreg 1125 = sn (lab x - 1) ∧ d₃.nreg 1118 = aM + x ∧
          d₃.nreg 1126 = 2 ∧
          (∀ r, r ≠ 1119 → r ≠ 1118 → r ≠ 1125 → r ≠ 1126 → d₃.nreg r = d₂.nreg r) ∧
          d₃.nmem = d₂.nmem ∧ k₃ = 5 := by
        have r01 := q2 1001 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        have r05 := q2 1105 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        have r19 := q2 1019 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        have r30 := q2 1130 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        exec_block
        · config_simp; rw [r05, h05, b19, r01, h01]; omega
        · config_simp; rw [r19, h19, b14]; omega
        · refine ⟨‹WordsBounded _ _›, ?_, ?_, ?_, ?_, fun r h1 h2 h3 h4 => by
            simp [h1, h2, h3, h4], rfl, rfl⟩
          · simp only [upd_apply, Nat.reduceEqDiff, ↓reduceIte]; rw [b19, r01, h01]
          · simp only [upd_apply, Nat.reduceEqDiff, ↓reduceIte]
            rw [r05, h05, b19, r01, h01, m₂, mS]
          · simp only [upd_apply, Nat.reduceEqDiff, ↓reduceIte]; rw [r19, h19, b14]
          · simp only [upd_apply, ↓reduceIte]; rw [r30, h30]
      have q3 : ∀ r, r ≠ 1110 → r ≠ 1114 → r ≠ 1118 → r ≠ 1119 → r ≠ 1125 → r ≠ 1126 →
          d₃.nreg r = d.nreg r := fun r a b c' e f' g' => by rw [q₃ r e c' f' g', q2 r a b c' e f' g']
      have r35 := q3 1135 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      have r34 := q3 1134 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      have r00 := q3 0 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      have r01 := q3 1001 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      have c10 : d₃.nreg 1110 = i := by
        rw [q₃ 1110 (by omega) (by omega) (by omega) (by omega), q₂ 1110 (by omega) (by omega)
          (by omega), h10]
      -- the if: the mark in `1126`
      obtain ⟨d₄, k₄, e₄, hw₄, c26', q₄, m₄, hk₄⟩ : ∃ d₄ k₄, Exec P W
          (.ifLtN 0 1135 (.ifLtN 1119 1134 .skip (.ifLtN 1134 1119 .skip
            (.instr (.copyN 1126 1001)))) (.ifLtN 0 1125 (.instr (.copyN 1126 1001)) .skip))
          d₃ d₄ k₄ ∧ WordsBounded W d₄ ∧ d₄.nreg 1126 = mkL lab sn mode kj x ∧
          (∀ r, r ≠ 1126 → d₄.nreg r = d₃.nreg r) ∧ d₄.nmem = d₃.nmem ∧ k₄ ≤ 6 := by
        have ec := Exec.copyN (P := P) hw₃ 1126 1001
        have v26 : (upd d₃.nreg 1126 (d₃.nreg 1001)) 1126 = 1 := by rw [upd_same, r01, h01]
        have vo : ∀ r, r ≠ 1126 → (upd d₃.nreg 1126 (d₃.nreg 1001)) r = d₃.nreg r :=
          fun r hr => upd_other _ _ _ hr
        by_cases hm : d₃.nreg 0 < d₃.nreg 1135
        · rw [r00, r35, h0, h35] at hm
          by_cases t1 : d₃.nreg 1119 < d₃.nreg 1134
          · rw [c19, r34, h34] at t1
            refine ⟨d₃, _, .ifLtN_true (by rw [r00, r35, h0, h35]; exact hm)
              (.ifLtN_true (by rw [c19, r34, h34]; exact t1) (.skip hw₃)), hw₃, ?_,
              fun _ _ => rfl, rfl, by omega⟩
            rw [c26]; unfold mkL; rw [iteF (by omega)]
          · by_cases t2 : d₃.nreg 1134 < d₃.nreg 1119
            · rw [c19, r34, h34] at t1 t2
              refine ⟨d₃, _, .ifLtN_true (by rw [r00, r35, h0, h35]; exact hm)
                (.ifLtN_false (by rw [c19, r34, h34]; exact t1)
                  (.ifLtN_true (by rw [c19, r34, h34]; exact t2) (.skip hw₃))), hw₃, ?_,
                fun _ _ => rfl, rfl, by omega⟩
              rw [c26]; unfold mkL; rw [iteF (by omega)]
            · rw [c19, r34, h34] at t1 t2
              refine ⟨_, _, .ifLtN_true (by rw [r00, r35, h0, h35]; exact hm)
                (.ifLtN_false (by rw [c19, r34, h34]; exact t1)
                  (.ifLtN_false (by rw [c19, r34, h34]; exact t2) ec)), ec.wb_right, ?_,
                vo, rfl, by omega⟩
              show upd d₃.nreg 1126 (d₃.nreg 1001) 1126 = _
              rw [v26]; unfold mkL; rw [iteT (Or.inl ⟨hm, by omega⟩)]
        · rw [r00, r35, h0, h35] at hm
          by_cases t3 : d₃.nreg 0 < d₃.nreg 1125
          · rw [r00, h0, c25] at t3
            refine ⟨_, _, .ifLtN_false (by rw [r00, r35, h0, h35]; exact hm)
              (.ifLtN_true (by rw [r00, h0, c25]; exact t3) ec), ec.wb_right, ?_, vo, rfl,
              by omega⟩
            show upd d₃.nreg 1126 (d₃.nreg 1001) 1126 = _
            rw [v26]; unfold mkL; rw [iteT (Or.inr ⟨hm, t3⟩)]
          · rw [r00, h0, c25] at t3
            refine ⟨d₃, _, .ifLtN_false (by rw [r00, r35, h0, h35]; exact hm)
              (.ifLtN_false (by rw [r00, h0, c25]; exact t3) (.skip hw₃)), hw₃, ?_,
              fun _ _ => rfl, rfl, by omega⟩
            rw [c26]; unfold mkL; rw [iteF (by omega)]
      -- the store and the next vertex
      have es := Exec.storeN (P := P) hw₄ 1118 1126
      have r4 : ∀ r, r ≠ 1126 → d₄.nreg r = d₃.nreg r := q₄
      have e5 := Exec.addN (P := P) es.wb_right 1110 1110 1001
        (by simp only; rw [r4 1110 (by omega), r4 1001 (by omega), c10, r01, h01]; omega)
      refine ⟨_, _, .seq e₂ (.seq e₃ (.seq e₄ (.seq es e5))), ⟨e5.wb_right, ?_, ?_,
        fun r a b c' e f' g' => ?_, fun y hy => ?_, fun a ha => ?_⟩, by omega⟩
      · simp only [upd_same]; rw [r4 1110 (by omega), r4 1001 (by omega), c10, r01, h01]
      · simp only [upd_other _ _ _ (show (1101:ℕ) ≠ 1110 by omega)]
        rw [r4 1101 (by omega), q3 1101 (by omega) (by omega) (by omega) (by omega) (by omega)
          (by omega), h1101]
      · simp only [upd_other _ _ _ a]
        rw [r4 r g', q3 r a b c' e f' g']
      · show upd d₄.nmem (d₄.nreg 1118) (d₄.nreg 1126) (aM + y) = _
        rw [r4 1118 (by omega), c18, c26', m₄, m₃, m₂]
        by_cases hyx : y = x
        · subst hyx; rw [upd_same, iteT ⟨i, Nat.lt_succ_self _, hxdef.symm⟩]
        · rw [upd_other _ _ _ (by omega), hmk y hy]
          congr 1
          apply propext
          constructor
          · rintro ⟨l, hl, e⟩; exact ⟨l, by omega, e⟩
          · rintro ⟨l, hl, e⟩
            refine ⟨l, ?_, e⟩
            rcases Nat.lt_succ_iff_lt_or_eq.1 hl with hl | rfl
            · exact hl
            · exact absurd (e.symm.trans hxdef.symm) hyx
      · show upd d₄.nmem (d₄.nreg 1118) (d₄.nreg 1126) a = _
        rw [r4 1118 (by omega), c18, upd_other _ _ _ (by omega), m₄, m₃, m₂]; exact hfr a ha)
    (Nat.zero_le _) hI₀
  obtain ⟨hw₁, -, -, hq₁, hmk₁, hfr₁⟩ := hI₁
  refine ⟨d₁, 1 + k₁, .seq e0 e₁, hw₁, fun x hx => ?_, hfr₁, hq₁, by omega⟩
  rw [hmk₁ x hx]
  by_cases h : x ∈ UN U
  · rw [iteT ((lv_mem_iff U).2 h), iteT h]
  · rw [iteF (fun h' => h ((lv_mem_iff U).1 h')), iteF h]

end Piece

end PlanarSeparator
